/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module topology.algebra.infinite_sum.basic
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Parity
import Mathbin.Logic.Encodable.Lattice
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Topology.Algebra.Star

/-!
# Infinite sum over a topological monoid

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This sum is known as unconditionally convergent, as it sums to the same value under all possible
permutations. For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute
convergence.

Note: There are summable sequences which are not unconditionally convergent! The other way holds
generally, see `has_sum.tendsto_sum_nat`.

## References

* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/


noncomputable section

open Classical Filter Finset Function

open BigOperators Classical Topology

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

section HasSum

variable [AddCommMonoid α] [TopologicalSpace α]

#print HasSum /-
/-- Infinite sum on a topological monoid

The `at_top` filter on `finset β` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is invariant under reordering. In particular,
the function `ℕ → ℝ` sending `n` to `(-1)^n / (n+1)` does not have a
sum for this definition, but a series which is absolutely convergent will have the correct sum.

This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).

For the definition or many statements, `α` does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant.
-/
def HasSum (f : β → α) (a : α) : Prop :=
  Tendsto (fun s : Finset β => ∑ b in s, f b) atTop (𝓝 a)
#align has_sum HasSum
-/

#print Summable /-
/-- `summable f` means that `f` has some (infinite) sum. Use `tsum` to get the value. -/
def Summable (f : β → α) : Prop :=
  ∃ a, HasSum f a
#align summable Summable
-/

#print tsum /-
/-- `∑' i, f i` is the sum of `f` it exists, or 0 otherwise -/
irreducible_def tsum {β} (f : β → α) :=
  if h : Summable f then Classical.choose h else 0
#align tsum tsum
-/

-- mathport name: «expr∑' , »
notation3"∑' "-- see Note [operator precedence of big operators]
(...)", "r:(scoped f => tsum f) => r

variable {f g : β → α} {a b : α} {s : Finset β}

/- warning: summable.has_sum -> Summable.hasSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α}, (Summable.{u1, u2} α β _inst_1 _inst_2 f) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 f (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α}, (Summable.{u2, u1} α β _inst_1 _inst_2 f) -> (HasSum.{u2, u1} α β _inst_1 _inst_2 f (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => f b)))
Case conversion may be inaccurate. Consider using '#align summable.has_sum Summable.hasSumₓ'. -/
theorem Summable.hasSum (ha : Summable f) : HasSum f (∑' b, f b) := by
  simp [ha, tsum] <;> exact some_spec ha
#align summable.has_sum Summable.hasSum

/- warning: has_sum.summable -> HasSum.summable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α}, (HasSum.{u1, u2} α β _inst_1 _inst_2 f a) -> (Summable.{u1, u2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α} {a : α}, (HasSum.{u2, u1} α β _inst_1 _inst_2 f a) -> (Summable.{u2, u1} α β _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align has_sum.summable HasSum.summableₓ'. -/
theorem HasSum.summable (h : HasSum f a) : Summable f :=
  ⟨a, h⟩
#align has_sum.summable HasSum.summable

/- warning: has_sum_zero -> hasSum_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α], HasSum.{u1, u2} α β _inst_1 _inst_2 (fun (b : β) => OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α], HasSum.{u2, u1} α β _inst_1 _inst_2 (fun (b : β) => OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align has_sum_zero hasSum_zeroₓ'. -/
/-- Constant zero function has sum `0` -/
theorem hasSum_zero : HasSum (fun b => 0 : β → α) 0 := by simp [HasSum, tendsto_const_nhds]
#align has_sum_zero hasSum_zero

/- warning: has_sum_empty -> hasSum_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} [_inst_3 : IsEmpty.{succ u2} β], HasSum.{u1, u2} α β _inst_1 _inst_2 f (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} [_inst_3 : IsEmpty.{succ u2} β], HasSum.{u1, u2} α β _inst_1 _inst_2 f (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align has_sum_empty hasSum_emptyₓ'. -/
theorem hasSum_empty [IsEmpty β] : HasSum f 0 := by convert hasSum_zero
#align has_sum_empty hasSum_empty

/- warning: summable_zero -> summable_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α], Summable.{u1, u2} α β _inst_1 _inst_2 (fun (b : β) => OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α], Summable.{u2, u1} α β _inst_1 _inst_2 (fun (b : β) => OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align summable_zero summable_zeroₓ'. -/
theorem summable_zero : Summable (fun b => 0 : β → α) :=
  hasSum_zero.Summable
#align summable_zero summable_zero

#print summable_empty /-
theorem summable_empty [IsEmpty β] : Summable f :=
  hasSum_empty.Summable
#align summable_empty summable_empty
-/

/- warning: tsum_eq_zero_of_not_summable -> tsum_eq_zero_of_not_summable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α}, (Not (Summable.{u1, u2} α β _inst_1 _inst_2 f)) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => f b)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α}, (Not (Summable.{u2, u1} α β _inst_1 _inst_2 f)) -> (Eq.{succ u2} α (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => f b)) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align tsum_eq_zero_of_not_summable tsum_eq_zero_of_not_summableₓ'. -/
theorem tsum_eq_zero_of_not_summable (h : ¬Summable f) : (∑' b, f b) = 0 := by simp [tsum, h]
#align tsum_eq_zero_of_not_summable tsum_eq_zero_of_not_summable

/- warning: summable_congr -> summable_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {g : β -> α}, (forall (b : β), Eq.{succ u1} α (f b) (g b)) -> (Iff (Summable.{u1, u2} α β _inst_1 _inst_2 f) (Summable.{u1, u2} α β _inst_1 _inst_2 g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α} {g : β -> α}, (forall (b : β), Eq.{succ u2} α (f b) (g b)) -> (Iff (Summable.{u2, u1} α β _inst_1 _inst_2 f) (Summable.{u2, u1} α β _inst_1 _inst_2 g))
Case conversion may be inaccurate. Consider using '#align summable_congr summable_congrₓ'. -/
theorem summable_congr (hfg : ∀ b, f b = g b) : Summable f ↔ Summable g :=
  iff_of_eq (congr_arg Summable <| funext hfg)
#align summable_congr summable_congr

/- warning: summable.congr -> Summable.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {g : β -> α}, (Summable.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (b : β), Eq.{succ u1} α (f b) (g b)) -> (Summable.{u1, u2} α β _inst_1 _inst_2 g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α} {g : β -> α}, (Summable.{u2, u1} α β _inst_1 _inst_2 f) -> (forall (b : β), Eq.{succ u2} α (f b) (g b)) -> (Summable.{u2, u1} α β _inst_1 _inst_2 g)
Case conversion may be inaccurate. Consider using '#align summable.congr Summable.congrₓ'. -/
theorem Summable.congr (hf : Summable f) (hfg : ∀ b, f b = g b) : Summable g :=
  (summable_congr hfg).mp hf
#align summable.congr Summable.congr

#print HasSum.hasSum_of_sum_eq /-
theorem HasSum.hasSum_of_sum_eq {g : γ → α}
    (h_eq :
      ∀ u : Finset γ,
        ∃ v : Finset β, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ (∑ x in u', g x) = ∑ b in v', f b)
    (hf : HasSum g a) : HasSum f a :=
  le_trans (map_atTop_finset_sum_le_of_sum_eq h_eq) hf
#align has_sum.has_sum_of_sum_eq HasSum.hasSum_of_sum_eq
-/

#print hasSum_iff_hasSum /-
theorem hasSum_iff_hasSum {g : γ → α}
    (h₁ :
      ∀ u : Finset γ,
        ∃ v : Finset β, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ (∑ x in u', g x) = ∑ b in v', f b)
    (h₂ :
      ∀ v : Finset β,
        ∃ u : Finset γ, ∀ u', u ⊆ u' → ∃ v', v ⊆ v' ∧ (∑ b in v', f b) = ∑ x in u', g x) :
    HasSum f a ↔ HasSum g a :=
  ⟨HasSum.hasSum_of_sum_eq h₂, HasSum.hasSum_of_sum_eq h₁⟩
#align has_sum_iff_has_sum hasSum_iff_hasSum
-/

/- warning: function.injective.has_sum_iff -> Function.Injective.hasSum_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {g : γ -> β}, (Function.Injective.{succ u3, succ u2} γ β g) -> (forall (x : β), (Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.range.{u2, succ u3} β γ g))) -> (Eq.{succ u1} α (f x) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))) -> (Iff (HasSum.{u1, u3} α γ _inst_1 _inst_2 (Function.comp.{succ u3, succ u2, succ u1} γ β α f g) a) (HasSum.{u1, u2} α β _inst_1 _inst_2 f a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {g : γ -> β}, (Function.Injective.{succ u3, succ u2} γ β g) -> (forall (x : β), (Not (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Set.range.{u2, succ u3} β γ g))) -> (Eq.{succ u1} α (f x) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))) -> (Iff (HasSum.{u1, u3} α γ _inst_1 _inst_2 (Function.comp.{succ u3, succ u2, succ u1} γ β α f g) a) (HasSum.{u1, u2} α β _inst_1 _inst_2 f a))
Case conversion may be inaccurate. Consider using '#align function.injective.has_sum_iff Function.Injective.hasSum_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ∉ » set.range[set.range] g) -/
theorem Function.Injective.hasSum_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ (x) (_ : x ∉ Set.range g), f x = 0) : HasSum (f ∘ g) a ↔ HasSum f a := by
  simp only [HasSum, tendsto, hg.map_at_top_finset_sum_eq hf]
#align function.injective.has_sum_iff Function.Injective.hasSum_iff

/- warning: function.injective.summable_iff -> Function.Injective.summable_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {g : γ -> β}, (Function.Injective.{succ u3, succ u2} γ β g) -> (forall (x : β), (Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.range.{u2, succ u3} β γ g))) -> (Eq.{succ u1} α (f x) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))) -> (Iff (Summable.{u1, u3} α γ _inst_1 _inst_2 (Function.comp.{succ u3, succ u2, succ u1} γ β α f g)) (Summable.{u1, u2} α β _inst_1 _inst_2 f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {g : γ -> β}, (Function.Injective.{succ u3, succ u2} γ β g) -> (forall (x : β), (Not (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Set.range.{u2, succ u3} β γ g))) -> (Eq.{succ u1} α (f x) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))) -> (Iff (Summable.{u1, u3} α γ _inst_1 _inst_2 (Function.comp.{succ u3, succ u2, succ u1} γ β α f g)) (Summable.{u1, u2} α β _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align function.injective.summable_iff Function.Injective.summable_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ∉ » set.range[set.range] g) -/
theorem Function.Injective.summable_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ (x) (_ : x ∉ Set.range g), f x = 0) : Summable (f ∘ g) ↔ Summable f :=
  exists_congr fun _ => hg.hasSum_iff hf
#align function.injective.summable_iff Function.Injective.summable_iff

/- warning: has_sum_subtype_iff_of_support_subset -> hasSum_subtype_iff_of_support_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {s : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f) s) -> (Iff (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))))) a) (HasSum.{u1, u2} α β _inst_1 _inst_2 f a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {s : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (Function.support.{u2, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f) s) -> (Iff (HasSum.{u1, u2} α (Set.Elem.{u2} β s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β s) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s))) a) (HasSum.{u1, u2} α β _inst_1 _inst_2 f a))
Case conversion may be inaccurate. Consider using '#align has_sum_subtype_iff_of_support_subset hasSum_subtype_iff_of_support_subsetₓ'. -/
theorem hasSum_subtype_iff_of_support_subset {s : Set β} (hf : support f ⊆ s) :
    HasSum (f ∘ coe : s → α) a ↔ HasSum f a :=
  Subtype.coe_injective.hasSum_iff <| by simpa using support_subset_iff'.1 hf
#align has_sum_subtype_iff_of_support_subset hasSum_subtype_iff_of_support_subset

/- warning: has_sum_subtype_iff_indicator -> hasSum_subtype_iff_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {s : Set.{u2} β}, Iff (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))))) a) (HasSum.{u1, u2} α β _inst_1 _inst_2 (Set.indicator.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) s f) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {s : Set.{u2} β}, Iff (HasSum.{u1, u2} α (Set.Elem.{u2} β s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β s) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s))) a) (HasSum.{u1, u2} α β _inst_1 _inst_2 (Set.indicator.{u2, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) s f) a)
Case conversion may be inaccurate. Consider using '#align has_sum_subtype_iff_indicator hasSum_subtype_iff_indicatorₓ'. -/
theorem hasSum_subtype_iff_indicator {s : Set β} :
    HasSum (f ∘ coe : s → α) a ↔ HasSum (s.indicator f) a := by
  rw [← Set.indicator_range_comp, Subtype.range_coe,
    hasSum_subtype_iff_of_support_subset Set.support_indicator_subset]
#align has_sum_subtype_iff_indicator hasSum_subtype_iff_indicator

/- warning: summable_subtype_iff_indicator -> summable_subtype_iff_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {s : Set.{u2} β}, Iff (Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s)))))))) (Summable.{u1, u2} α β _inst_1 _inst_2 (Set.indicator.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) s f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {s : Set.{u2} β}, Iff (Summable.{u1, u2} α (Set.Elem.{u2} β s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β s) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s)))) (Summable.{u1, u2} α β _inst_1 _inst_2 (Set.indicator.{u2, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) s f))
Case conversion may be inaccurate. Consider using '#align summable_subtype_iff_indicator summable_subtype_iff_indicatorₓ'. -/
theorem summable_subtype_iff_indicator {s : Set β} :
    Summable (f ∘ coe : s → α) ↔ Summable (s.indicator f) :=
  exists_congr fun _ => hasSum_subtype_iff_indicator
#align summable_subtype_iff_indicator summable_subtype_iff_indicator

/- warning: has_sum_subtype_support -> hasSum_subtype_support is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α}, Iff (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)))))))) a) (HasSum.{u1, u2} α β _inst_1 _inst_2 f a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α} {a : α}, Iff (HasSum.{u2, u1} α (Set.Elem.{u1} β (Function.support.{u1, u2} β α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) f)) _inst_1 _inst_2 (Function.comp.{succ u1, succ u1, succ u2} (Set.Elem.{u1} β (Function.support.{u1, u2} β α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) f)) β α f (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Function.support.{u1, u2} β α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) f)))) a) (HasSum.{u2, u1} α β _inst_1 _inst_2 f a)
Case conversion may be inaccurate. Consider using '#align has_sum_subtype_support hasSum_subtype_supportₓ'. -/
@[simp]
theorem hasSum_subtype_support : HasSum (f ∘ coe : support f → α) a ↔ HasSum f a :=
  hasSum_subtype_iff_of_support_subset <| Set.Subset.refl _
#align has_sum_subtype_support hasSum_subtype_support

#print hasSum_fintype /-
theorem hasSum_fintype [Fintype β] (f : β → α) : HasSum f (∑ b, f b) :=
  OrderTop.tendsto_atTop_nhds _
#align has_sum_fintype hasSum_fintype
-/

#print Finset.hasSum /-
protected theorem Finset.hasSum (s : Finset β) (f : β → α) :
    HasSum (f ∘ coe : (↑s : Set β) → α) (∑ b in s, f b) :=
  by
  rw [← sum_attach]
  exact hasSum_fintype _
#align finset.has_sum Finset.hasSum
-/

#print Finset.summable /-
protected theorem Finset.summable (s : Finset β) (f : β → α) :
    Summable (f ∘ coe : (↑s : Set β) → α) :=
  (s.HasSum f).Summable
#align finset.summable Finset.summable
-/

#print Set.Finite.summable /-
protected theorem Set.Finite.summable {s : Set β} (hs : s.Finite) (f : β → α) :
    Summable (f ∘ coe : s → α) := by
  convert hs.to_finset.summable f <;> simp only [hs.coe_to_finset]
#align set.finite.summable Set.Finite.summable
-/

/- warning: has_sum_sum_of_ne_finset_zero -> hasSum_sum_of_ne_finset_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {s : Finset.{u2} β}, (forall (b : β), (Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s)) -> (Eq.{succ u1} α (f b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 f (Finset.sum.{u1, u2} α β _inst_1 s (fun (b : β) => f b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {s : Finset.{u2} β}, (forall (b : β), (Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s)) -> (Eq.{succ u1} α (f b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 f (Finset.sum.{u1, u2} α β _inst_1 s (fun (b : β) => f b)))
Case conversion may be inaccurate. Consider using '#align has_sum_sum_of_ne_finset_zero hasSum_sum_of_ne_finset_zeroₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (b «expr ∉ » s) -/
/-- If a function `f` vanishes outside of a finite set `s`, then it `has_sum` `∑ b in s, f b`. -/
theorem hasSum_sum_of_ne_finset_zero (hf : ∀ (b) (_ : b ∉ s), f b = 0) : HasSum f (∑ b in s, f b) :=
  (hasSum_subtype_iff_of_support_subset <| support_subset_iff'.2 hf).1 <| s.HasSum f
#align has_sum_sum_of_ne_finset_zero hasSum_sum_of_ne_finset_zero

/- warning: summable_of_ne_finset_zero -> summable_of_ne_finset_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {s : Finset.{u2} β}, (forall (b : β), (Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s)) -> (Eq.{succ u1} α (f b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))) -> (Summable.{u1, u2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {s : Finset.{u2} β}, (forall (b : β), (Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s)) -> (Eq.{succ u1} α (f b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))) -> (Summable.{u1, u2} α β _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align summable_of_ne_finset_zero summable_of_ne_finset_zeroₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (b «expr ∉ » s) -/
theorem summable_of_ne_finset_zero (hf : ∀ (b) (_ : b ∉ s), f b = 0) : Summable f :=
  (hasSum_sum_of_ne_finset_zero hf).Summable
#align summable_of_ne_finset_zero summable_of_ne_finset_zero

/- warning: has_sum_single -> hasSum_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} (b : β), (forall (b' : β), (Ne.{succ u2} β b' b) -> (Eq.{succ u1} α (f b') (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 f (f b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} (b : β), (forall (b' : β), (Ne.{succ u2} β b' b) -> (Eq.{succ u1} α (f b') (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 f (f b))
Case conversion may be inaccurate. Consider using '#align has_sum_single hasSum_singleₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (b' «expr ≠ » b) -/
theorem hasSum_single {f : β → α} (b : β) (hf : ∀ (b') (_ : b' ≠ b), f b' = 0) : HasSum f (f b) :=
  suffices HasSum f (∑ b' in {b}, f b') by simpa using this
  hasSum_sum_of_ne_finset_zero <| by simpa [hf]
#align has_sum_single hasSum_single

/- warning: has_sum_ite_eq -> hasSum_ite_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] (b : β) [_inst_3 : DecidablePred.{succ u2} β (fun (_x : β) => Eq.{succ u2} β _x b)] (a : α), HasSum.{u1, u2} α β _inst_1 _inst_2 (fun (b' : β) => ite.{succ u1} α (Eq.{succ u2} β b' b) (_inst_3 b') a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))))) a
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] (b : β) [_inst_3 : DecidablePred.{succ u2} β (fun (_x : β) => Eq.{succ u2} β _x b)] (a : α), HasSum.{u1, u2} α β _inst_1 _inst_2 (fun (b' : β) => ite.{succ u1} α (Eq.{succ u2} β b' b) (_inst_3 b') a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))) a
Case conversion may be inaccurate. Consider using '#align has_sum_ite_eq hasSum_ite_eqₓ'. -/
theorem hasSum_ite_eq (b : β) [DecidablePred (· = b)] (a : α) :
    HasSum (fun b' => if b' = b then a else 0) a :=
  by
  convert hasSum_single b _
  · exact (if_pos rfl).symm
  intro b' hb'
  exact if_neg hb'
#align has_sum_ite_eq hasSum_ite_eq

/- warning: has_sum_pi_single -> hasSum_pi_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : DecidableEq.{succ u2} β] (b : β) (a : α), HasSum.{u1, u2} α β _inst_1 _inst_2 (Pi.single.{u2, u1} β (fun (b : β) => α) (fun (a : β) (b : β) => _inst_3 a b) (fun (i : β) => AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) b a) a
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : DecidableEq.{succ u2} β] (b : β) (a : α), HasSum.{u1, u2} α β _inst_1 _inst_2 (Pi.single.{u2, u1} β (fun (b : β) => α) (fun (a : β) (b : β) => _inst_3 a b) (fun (i : β) => AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) b a) a
Case conversion may be inaccurate. Consider using '#align has_sum_pi_single hasSum_pi_singleₓ'. -/
theorem hasSum_pi_single [DecidableEq β] (b : β) (a : α) : HasSum (Pi.single b a) a :=
  show HasSum (fun x => Pi.single b a x) a by simpa only [Pi.single_apply] using hasSum_ite_eq b a
#align has_sum_pi_single hasSum_pi_single

#print Equiv.hasSum_iff /-
theorem Equiv.hasSum_iff (e : γ ≃ β) : HasSum (f ∘ e) a ↔ HasSum f a :=
  e.Injective.hasSum_iff <| by simp
#align equiv.has_sum_iff Equiv.hasSum_iff
-/

#print Function.Injective.hasSum_range_iff /-
theorem Function.Injective.hasSum_range_iff {g : γ → β} (hg : Injective g) :
    HasSum (fun x : Set.range g => f x) a ↔ HasSum (f ∘ g) a :=
  (Equiv.ofInjective g hg).hasSum_iff.symm
#align function.injective.has_sum_range_iff Function.Injective.hasSum_range_iff
-/

#print Equiv.summable_iff /-
theorem Equiv.summable_iff (e : γ ≃ β) : Summable (f ∘ e) ↔ Summable f :=
  exists_congr fun a => e.hasSum_iff
#align equiv.summable_iff Equiv.summable_iff
-/

/- warning: summable.prod_symm -> Summable.prod_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : (Prod.{u2, u3} β γ) -> α}, (Summable.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 _inst_2 f) -> (Summable.{u1, max u3 u2} α (Prod.{u3, u2} γ β) _inst_1 _inst_2 (fun (p : Prod.{u3, u2} γ β) => f (Prod.swap.{u3, u2} γ β p)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : (Prod.{u3, u2} β γ) -> α}, (Summable.{u1, max u3 u2} α (Prod.{u3, u2} β γ) _inst_1 _inst_2 f) -> (Summable.{u1, max u3 u2} α (Prod.{u2, u3} γ β) _inst_1 _inst_2 (fun (p : Prod.{u2, u3} γ β) => f (Prod.swap.{u2, u3} γ β p)))
Case conversion may be inaccurate. Consider using '#align summable.prod_symm Summable.prod_symmₓ'. -/
theorem Summable.prod_symm {f : β × γ → α} (hf : Summable f) : Summable fun p : γ × β => f p.symm :=
  (Equiv.prodComm γ β).summable_iff.2 hf
#align summable.prod_symm Summable.prod_symm

/- warning: equiv.has_sum_iff_of_support -> Equiv.hasSum_iff_of_support is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {g : γ -> α} (e : Equiv.{succ u2, succ u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g))), (forall (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)), Eq.{succ u1} α (g ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)))))) (coeFn.{max 1 (max (succ u2) (succ u3)) (succ u3) (succ u2), max (succ u2) (succ u3)} (Equiv.{succ u2, succ u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g))) (fun (_x : Equiv.{succ u2, succ u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g))) => (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) -> (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g))) (Equiv.hasCoeToFun.{succ u2, succ u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g))) e x))) (f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)))))) x))) -> (Iff (HasSum.{u1, u2} α β _inst_1 _inst_2 f a) (HasSum.{u1, u3} α γ _inst_1 _inst_2 g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {g : γ -> α} (e : Equiv.{succ u3, succ u2} (Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) (Set.Elem.{u2} γ (Function.support.{u2, u1} γ α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) g))), (forall (x : Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)), Eq.{succ u1} α (g (Subtype.val.{succ u2} γ (fun (x : γ) => Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) x (Function.support.{u2, u1} γ α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) g)) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Equiv.{succ u3, succ u2} (Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) (Set.Elem.{u2} γ (Function.support.{u2, u1} γ α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) g))) (Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) (fun (_x : Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) => Set.Elem.{u2} γ (Function.support.{u2, u1} γ α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) g)) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u2} (Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) (Set.Elem.{u2} γ (Function.support.{u2, u1} γ α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) g))) e x))) (f (Subtype.val.{succ u3} β (fun (x : β) => Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) x (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) x))) -> (Iff (HasSum.{u1, u3} α β _inst_1 _inst_2 f a) (HasSum.{u1, u2} α γ _inst_1 _inst_2 g a))
Case conversion may be inaccurate. Consider using '#align equiv.has_sum_iff_of_support Equiv.hasSum_iff_of_supportₓ'. -/
theorem Equiv.hasSum_iff_of_support {g : γ → α} (e : support f ≃ support g)
    (he : ∀ x : support f, g (e x) = f x) : HasSum f a ↔ HasSum g a :=
  by
  have : (g ∘ coe) ∘ e = f ∘ coe := funext he
  rw [← hasSum_subtype_support, ← this, e.has_sum_iff, hasSum_subtype_support]
#align equiv.has_sum_iff_of_support Equiv.hasSum_iff_of_support

/- warning: has_sum_iff_has_sum_of_ne_zero_bij -> hasSum_iff_hasSum_of_ne_zero_bij is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {g : γ -> α} (i : (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) -> β), (forall {{x : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)}} {{y : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)}}, (Eq.{succ u2} β (i x) (i y)) -> (Eq.{succ u3} γ ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)))))) x) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)))))) y))) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f) (Set.range.{u2, succ u3} β (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) i)) -> (forall (x : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)), Eq.{succ u1} α (f (i x)) (g ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)))))) x))) -> (Iff (HasSum.{u1, u2} α β _inst_1 _inst_2 f a) (HasSum.{u1, u3} α γ _inst_1 _inst_2 g a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α} {a : α} {g : γ -> α} (i : (Set.Elem.{u3} γ (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)) -> β), (forall {{x : Set.Elem.{u3} γ (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)}} {{y : Set.Elem.{u3} γ (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)}}, (Eq.{succ u1} β (i x) (i y)) -> (Eq.{succ u3} γ (Subtype.val.{succ u3} γ (fun (x : γ) => Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) x (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)) x) (Subtype.val.{succ u3} γ (fun (x : γ) => Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) x (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)) y))) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Function.support.{u1, u2} β α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) f) (Set.range.{u1, succ u3} β (Set.Elem.{u3} γ (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)) i)) -> (forall (x : Set.Elem.{u3} γ (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)), Eq.{succ u2} α (f (i x)) (g (Subtype.val.{succ u3} γ (fun (x : γ) => Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) x (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)) x))) -> (Iff (HasSum.{u2, u1} α β _inst_1 _inst_2 f a) (HasSum.{u2, u3} α γ _inst_1 _inst_2 g a))
Case conversion may be inaccurate. Consider using '#align has_sum_iff_has_sum_of_ne_zero_bij hasSum_iff_hasSum_of_ne_zero_bijₓ'. -/
theorem hasSum_iff_hasSum_of_ne_zero_bij {g : γ → α} (i : support g → β)
    (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y) (hf : support f ⊆ Set.range i)
    (hfg : ∀ x, f (i x) = g x) : HasSum f a ↔ HasSum g a :=
  Iff.symm <|
    Equiv.hasSum_iff_of_support
      (Equiv.ofBijective (fun x => ⟨i x, fun hx => x.coe_prop <| hfg x ▸ hx⟩)
        ⟨fun x y h => Subtype.ext <| hi <| Subtype.ext_iff.1 h, fun y =>
          (hf y.coe_prop).imp fun x hx => Subtype.ext hx⟩)
      hfg
#align has_sum_iff_has_sum_of_ne_zero_bij hasSum_iff_hasSum_of_ne_zero_bij

/- warning: equiv.summable_iff_of_support -> Equiv.summable_iff_of_support is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {g : γ -> α} (e : Equiv.{succ u2, succ u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g))), (forall (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)), Eq.{succ u1} α (g ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)))))) (coeFn.{max 1 (max (succ u2) (succ u3)) (succ u3) (succ u2), max (succ u2) (succ u3)} (Equiv.{succ u2, succ u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g))) (fun (_x : Equiv.{succ u2, succ u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g))) => (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) -> (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g))) (Equiv.hasCoeToFun.{succ u2, succ u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g))) e x))) (f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)))))) x))) -> (Iff (Summable.{u1, u2} α β _inst_1 _inst_2 f) (Summable.{u1, u3} α γ _inst_1 _inst_2 g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {g : γ -> α} (e : Equiv.{succ u3, succ u2} (Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) (Set.Elem.{u2} γ (Function.support.{u2, u1} γ α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) g))), (forall (x : Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)), Eq.{succ u1} α (g (Subtype.val.{succ u2} γ (fun (x : γ) => Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) x (Function.support.{u2, u1} γ α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) g)) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Equiv.{succ u3, succ u2} (Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) (Set.Elem.{u2} γ (Function.support.{u2, u1} γ α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) g))) (Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) (fun (_x : Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) => Set.Elem.{u2} γ (Function.support.{u2, u1} γ α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) g)) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u2} (Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) (Set.Elem.{u2} γ (Function.support.{u2, u1} γ α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) g))) e x))) (f (Subtype.val.{succ u3} β (fun (x : β) => Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) x (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) x))) -> (Iff (Summable.{u1, u3} α β _inst_1 _inst_2 f) (Summable.{u1, u2} α γ _inst_1 _inst_2 g))
Case conversion may be inaccurate. Consider using '#align equiv.summable_iff_of_support Equiv.summable_iff_of_supportₓ'. -/
theorem Equiv.summable_iff_of_support {g : γ → α} (e : support f ≃ support g)
    (he : ∀ x : support f, g (e x) = f x) : Summable f ↔ Summable g :=
  exists_congr fun _ => e.hasSum_iff_of_support he
#align equiv.summable_iff_of_support Equiv.summable_iff_of_support

/- warning: has_sum.map -> HasSum.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} [_inst_3 : AddCommMonoid.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ], (HasSum.{u1, u2} α β _inst_1 _inst_2 f a) -> (forall {G : Type.{u4}} [_inst_5 : AddMonoidHomClass.{u4, u1, u3} G α γ (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))] (g : G), (Continuous.{u1, u3} α γ _inst_2 _inst_4 (coeFn.{succ u4, max (succ u1) (succ u3)} G (fun (_x : G) => α -> γ) (FunLike.hasCoeToFun.{succ u4, succ u1, succ u3} G α (fun (_x : α) => γ) (AddHomClass.toFunLike.{u4, u1, u3} G α γ (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u4, u1, u3} G α γ (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3)) _inst_5))) g)) -> (HasSum.{u3, u2} γ β _inst_3 _inst_4 (Function.comp.{succ u2, succ u1, succ u3} β α γ (coeFn.{succ u4, max (succ u1) (succ u3)} G (fun (_x : G) => α -> γ) (FunLike.hasCoeToFun.{succ u4, succ u1, succ u3} G α (fun (_x : α) => γ) (AddHomClass.toFunLike.{u4, u1, u3} G α γ (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u4, u1, u3} G α γ (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3)) _inst_5))) g) f) (coeFn.{succ u4, max (succ u1) (succ u3)} G (fun (_x : G) => α -> γ) (FunLike.hasCoeToFun.{succ u4, succ u1, succ u3} G α (fun (_x : α) => γ) (AddHomClass.toFunLike.{u4, u1, u3} G α γ (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u4, u1, u3} G α γ (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3)) _inst_5))) g a)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u4}} [_inst_1 : AddCommMonoid.{u3} α] [_inst_2 : TopologicalSpace.{u3} α] {f : β -> α} {a : α} [_inst_3 : AddCommMonoid.{u4} γ] [_inst_4 : TopologicalSpace.{u4} γ], (HasSum.{u3, u2} α β _inst_1 _inst_2 f a) -> (forall {G : Type.{u1}} [_inst_5 : AddMonoidHomClass.{u1, u3, u4} G α γ (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1)) (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3))] (g : G), (Continuous.{u3, u4} α γ _inst_2 _inst_4 (FunLike.coe.{succ u1, succ u3, succ u4} G α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => γ) _x) (AddHomClass.toFunLike.{u1, u3, u4} G α γ (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1))) (AddZeroClass.toAdd.{u4} γ (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u1, u3, u4} G α γ (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1)) (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3)) _inst_5)) g)) -> (HasSum.{u4, u2} γ β _inst_3 _inst_4 (Function.comp.{succ u2, succ u3, succ u4} β α γ (FunLike.coe.{succ u1, succ u3, succ u4} G α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => γ) _x) (AddHomClass.toFunLike.{u1, u3, u4} G α γ (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1))) (AddZeroClass.toAdd.{u4} γ (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u1, u3, u4} G α γ (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1)) (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3)) _inst_5)) g) f) (FunLike.coe.{succ u1, succ u3, succ u4} G α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => γ) _x) (AddHomClass.toFunLike.{u1, u3, u4} G α γ (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1))) (AddZeroClass.toAdd.{u4} γ (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u1, u3, u4} G α γ (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1)) (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3)) _inst_5)) g a)))
Case conversion may be inaccurate. Consider using '#align has_sum.map HasSum.mapₓ'. -/
protected theorem HasSum.map [AddCommMonoid γ] [TopologicalSpace γ] (hf : HasSum f a) {G}
    [AddMonoidHomClass G α γ] (g : G) (hg : Continuous g) : HasSum (g ∘ f) (g a) :=
  have : (g ∘ fun s : Finset β => ∑ b in s, f b) = fun s : Finset β => ∑ b in s, g (f b) :=
    funext <| map_sum g _
  show Tendsto (fun s : Finset β => ∑ b in s, g (f b)) atTop (𝓝 (g a)) from
    this ▸ (hg.Tendsto a).comp hf
#align has_sum.map HasSum.map

/- warning: summable.map -> Summable.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} [_inst_3 : AddCommMonoid.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ], (Summable.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {G : Type.{u4}} [_inst_5 : AddMonoidHomClass.{u4, u1, u3} G α γ (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))] (g : G), (Continuous.{u1, u3} α γ _inst_2 _inst_4 (coeFn.{succ u4, max (succ u1) (succ u3)} G (fun (_x : G) => α -> γ) (FunLike.hasCoeToFun.{succ u4, succ u1, succ u3} G α (fun (_x : α) => γ) (AddHomClass.toFunLike.{u4, u1, u3} G α γ (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u4, u1, u3} G α γ (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3)) _inst_5))) g)) -> (Summable.{u3, u2} γ β _inst_3 _inst_4 (Function.comp.{succ u2, succ u1, succ u3} β α γ (coeFn.{succ u4, max (succ u1) (succ u3)} G (fun (_x : G) => α -> γ) (FunLike.hasCoeToFun.{succ u4, succ u1, succ u3} G α (fun (_x : α) => γ) (AddHomClass.toFunLike.{u4, u1, u3} G α γ (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u4, u1, u3} G α γ (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3)) _inst_5))) g) f)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u4}} [_inst_1 : AddCommMonoid.{u3} α] [_inst_2 : TopologicalSpace.{u3} α] {f : β -> α} [_inst_3 : AddCommMonoid.{u4} γ] [_inst_4 : TopologicalSpace.{u4} γ], (Summable.{u3, u2} α β _inst_1 _inst_2 f) -> (forall {G : Type.{u1}} [_inst_5 : AddMonoidHomClass.{u1, u3, u4} G α γ (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1)) (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3))] (g : G), (Continuous.{u3, u4} α γ _inst_2 _inst_4 (FunLike.coe.{succ u1, succ u3, succ u4} G α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => γ) _x) (AddHomClass.toFunLike.{u1, u3, u4} G α γ (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1))) (AddZeroClass.toAdd.{u4} γ (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u1, u3, u4} G α γ (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1)) (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3)) _inst_5)) g)) -> (Summable.{u4, u2} γ β _inst_3 _inst_4 (Function.comp.{succ u2, succ u3, succ u4} β α γ (FunLike.coe.{succ u1, succ u3, succ u4} G α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => γ) _x) (AddHomClass.toFunLike.{u1, u3, u4} G α γ (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1))) (AddZeroClass.toAdd.{u4} γ (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u1, u3, u4} G α γ (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1)) (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3)) _inst_5)) g) f)))
Case conversion may be inaccurate. Consider using '#align summable.map Summable.mapₓ'. -/
protected theorem Summable.map [AddCommMonoid γ] [TopologicalSpace γ] (hf : Summable f) {G}
    [AddMonoidHomClass G α γ] (g : G) (hg : Continuous g) : Summable (g ∘ f) :=
  (hf.HasSum.map g hg).Summable
#align summable.map Summable.map

/- warning: summable.map_iff_of_left_inverse -> Summable.map_iff_of_leftInverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} [_inst_3 : AddCommMonoid.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] {G : Type.{u4}} {G' : Type.{u5}} [_inst_5 : AddMonoidHomClass.{u4, u1, u3} G α γ (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))] [_inst_6 : AddMonoidHomClass.{u5, u3, u1} G' γ α (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3)) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))] (g : G) (g' : G'), (Continuous.{u1, u3} α γ _inst_2 _inst_4 (coeFn.{succ u4, max (succ u1) (succ u3)} G (fun (_x : G) => α -> γ) (FunLike.hasCoeToFun.{succ u4, succ u1, succ u3} G α (fun (_x : α) => γ) (AddHomClass.toFunLike.{u4, u1, u3} G α γ (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u4, u1, u3} G α γ (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3)) _inst_5))) g)) -> (Continuous.{u3, u1} γ α _inst_4 _inst_2 (coeFn.{succ u5, max (succ u3) (succ u1)} G' (fun (_x : G') => γ -> α) (FunLike.hasCoeToFun.{succ u5, succ u3, succ u1} G' γ (fun (_x : γ) => α) (AddHomClass.toFunLike.{u5, u3, u1} G' γ α (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (AddMonoidHomClass.toAddHomClass.{u5, u3, u1} G' γ α (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3)) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) _inst_6))) g')) -> (Function.LeftInverse.{succ u1, succ u3} α γ (coeFn.{succ u5, max (succ u3) (succ u1)} G' (fun (_x : G') => γ -> α) (FunLike.hasCoeToFun.{succ u5, succ u3, succ u1} G' γ (fun (_x : γ) => α) (AddHomClass.toFunLike.{u5, u3, u1} G' γ α (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (AddMonoidHomClass.toAddHomClass.{u5, u3, u1} G' γ α (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3)) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) _inst_6))) g') (coeFn.{succ u4, max (succ u1) (succ u3)} G (fun (_x : G) => α -> γ) (FunLike.hasCoeToFun.{succ u4, succ u1, succ u3} G α (fun (_x : α) => γ) (AddHomClass.toFunLike.{u4, u1, u3} G α γ (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u4, u1, u3} G α γ (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3)) _inst_5))) g)) -> (Iff (Summable.{u3, u2} γ β _inst_3 _inst_4 (Function.comp.{succ u2, succ u1, succ u3} β α γ (coeFn.{succ u4, max (succ u1) (succ u3)} G (fun (_x : G) => α -> γ) (FunLike.hasCoeToFun.{succ u4, succ u1, succ u3} G α (fun (_x : α) => γ) (AddHomClass.toFunLike.{u4, u1, u3} G α γ (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u4, u1, u3} G α γ (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3)) _inst_5))) g) f)) (Summable.{u1, u2} α β _inst_1 _inst_2 f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u5}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α} [_inst_3 : AddCommMonoid.{u5} γ] [_inst_4 : TopologicalSpace.{u5} γ] {G : Type.{u4}} {G' : Type.{u3}} [_inst_5 : AddMonoidHomClass.{u4, u2, u5} G α γ (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) (AddMonoid.toAddZeroClass.{u5} γ (AddCommMonoid.toAddMonoid.{u5} γ _inst_3))] [_inst_6 : AddMonoidHomClass.{u3, u5, u2} G' γ α (AddMonoid.toAddZeroClass.{u5} γ (AddCommMonoid.toAddMonoid.{u5} γ _inst_3)) (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))] (g : G) (g' : G'), (Continuous.{u2, u5} α γ _inst_2 _inst_4 (FunLike.coe.{succ u4, succ u2, succ u5} G α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => γ) _x) (AddHomClass.toFunLike.{u4, u2, u5} G α γ (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))) (AddZeroClass.toAdd.{u5} γ (AddMonoid.toAddZeroClass.{u5} γ (AddCommMonoid.toAddMonoid.{u5} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u4, u2, u5} G α γ (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) (AddMonoid.toAddZeroClass.{u5} γ (AddCommMonoid.toAddMonoid.{u5} γ _inst_3)) _inst_5)) g)) -> (Continuous.{u5, u2} γ α _inst_4 _inst_2 (FunLike.coe.{succ u3, succ u5, succ u2} G' γ (fun (_x : γ) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : γ) => α) _x) (AddHomClass.toFunLike.{u3, u5, u2} G' γ α (AddZeroClass.toAdd.{u5} γ (AddMonoid.toAddZeroClass.{u5} γ (AddCommMonoid.toAddMonoid.{u5} γ _inst_3))) (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))) (AddMonoidHomClass.toAddHomClass.{u3, u5, u2} G' γ α (AddMonoid.toAddZeroClass.{u5} γ (AddCommMonoid.toAddMonoid.{u5} γ _inst_3)) (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) _inst_6)) g')) -> (Function.LeftInverse.{succ u2, succ u5} α γ (FunLike.coe.{succ u3, succ u5, succ u2} G' γ (fun (_x : γ) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : γ) => α) _x) (AddHomClass.toFunLike.{u3, u5, u2} G' γ α (AddZeroClass.toAdd.{u5} γ (AddMonoid.toAddZeroClass.{u5} γ (AddCommMonoid.toAddMonoid.{u5} γ _inst_3))) (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))) (AddMonoidHomClass.toAddHomClass.{u3, u5, u2} G' γ α (AddMonoid.toAddZeroClass.{u5} γ (AddCommMonoid.toAddMonoid.{u5} γ _inst_3)) (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) _inst_6)) g') (FunLike.coe.{succ u4, succ u2, succ u5} G α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => γ) _x) (AddHomClass.toFunLike.{u4, u2, u5} G α γ (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))) (AddZeroClass.toAdd.{u5} γ (AddMonoid.toAddZeroClass.{u5} γ (AddCommMonoid.toAddMonoid.{u5} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u4, u2, u5} G α γ (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) (AddMonoid.toAddZeroClass.{u5} γ (AddCommMonoid.toAddMonoid.{u5} γ _inst_3)) _inst_5)) g)) -> (Iff (Summable.{u5, u1} γ β _inst_3 _inst_4 (Function.comp.{succ u1, succ u2, succ u5} β α γ (FunLike.coe.{succ u4, succ u2, succ u5} G α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => γ) _x) (AddHomClass.toFunLike.{u4, u2, u5} G α γ (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))) (AddZeroClass.toAdd.{u5} γ (AddMonoid.toAddZeroClass.{u5} γ (AddCommMonoid.toAddMonoid.{u5} γ _inst_3))) (AddMonoidHomClass.toAddHomClass.{u4, u2, u5} G α γ (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) (AddMonoid.toAddZeroClass.{u5} γ (AddCommMonoid.toAddMonoid.{u5} γ _inst_3)) _inst_5)) g) f)) (Summable.{u2, u1} α β _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align summable.map_iff_of_left_inverse Summable.map_iff_of_leftInverseₓ'. -/
protected theorem Summable.map_iff_of_leftInverse [AddCommMonoid γ] [TopologicalSpace γ] {G G'}
    [AddMonoidHomClass G α γ] [AddMonoidHomClass G' γ α] (g : G) (g' : G') (hg : Continuous g)
    (hg' : Continuous g') (hinv : Function.LeftInverse g' g) : Summable (g ∘ f) ↔ Summable f :=
  ⟨fun h => by
    have := h.map _ hg'
    rwa [← Function.comp.assoc, hinv.id] at this, fun h => h.map _ hg⟩
#align summable.map_iff_of_left_inverse Summable.map_iff_of_leftInverse

/- warning: summable.map_iff_of_equiv -> Summable.map_iff_of_equiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} [_inst_3 : AddCommMonoid.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] {G : Type.{u4}} [_inst_5 : AddEquivClass.{u4, u1, u3} G α γ (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3)))] (g : G), (Continuous.{u1, u3} α γ _inst_2 _inst_4 (coeFn.{succ u4, max (succ u1) (succ u3)} G (fun (_x : G) => α -> γ) (FunLike.hasCoeToFun.{succ u4, succ u1, succ u3} G α (fun (_x : α) => γ) (EmbeddingLike.toFunLike.{succ u4, succ u1, succ u3} G α γ (EquivLike.toEmbeddingLike.{succ u4, succ u1, succ u3} G α γ (AddEquivClass.toEquivLike.{u4, u1, u3} G α γ (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))) _inst_5)))) g)) -> (Continuous.{u3, u1} γ α _inst_4 _inst_2 (AddEquivClass.inv.{u4, u1, u3} G α γ (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))) _inst_5 g)) -> (Iff (Summable.{u3, u2} γ β _inst_3 _inst_4 (Function.comp.{succ u2, succ u1, succ u3} β α γ (coeFn.{succ u4, max (succ u1) (succ u3)} G (fun (_x : G) => α -> γ) (FunLike.hasCoeToFun.{succ u4, succ u1, succ u3} G α (fun (_x : α) => γ) (EmbeddingLike.toFunLike.{succ u4, succ u1, succ u3} G α γ (EquivLike.toEmbeddingLike.{succ u4, succ u1, succ u3} G α γ (AddEquivClass.toEquivLike.{u4, u1, u3} G α γ (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ _inst_3))) _inst_5)))) g) f)) (Summable.{u1, u2} α β _inst_1 _inst_2 f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u4}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α} [_inst_3 : AddCommMonoid.{u4} γ] [_inst_4 : TopologicalSpace.{u4} γ] {G : Type.{u3}} [_inst_5 : AddEquivClass.{u3, u2, u4} G α γ (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))) (AddZeroClass.toAdd.{u4} γ (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3)))] (g : G), (Continuous.{u2, u4} α γ _inst_2 _inst_4 (FunLike.coe.{succ u3, succ u2, succ u4} G α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) _x) (EmbeddingLike.toFunLike.{succ u3, succ u2, succ u4} G α γ (EquivLike.toEmbeddingLike.{succ u3, succ u2, succ u4} G α γ (AddEquivClass.toEquivLike.{u3, u2, u4} G α γ (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))) (AddZeroClass.toAdd.{u4} γ (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3))) _inst_5))) g)) -> (Continuous.{u4, u2} γ α _inst_4 _inst_2 (EquivLike.inv.{succ u3, succ u2, succ u4} G α γ (AddEquivClass.toEquivLike.{u3, u2, u4} G α γ (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))) (AddZeroClass.toAdd.{u4} γ (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3))) _inst_5) g)) -> (Iff (Summable.{u4, u1} γ β _inst_3 _inst_4 (Function.comp.{succ u1, succ u2, succ u4} β α γ (FunLike.coe.{succ u3, succ u2, succ u4} G α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) _x) (EmbeddingLike.toFunLike.{succ u3, succ u2, succ u4} G α γ (EquivLike.toEmbeddingLike.{succ u3, succ u2, succ u4} G α γ (AddEquivClass.toEquivLike.{u3, u2, u4} G α γ (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))) (AddZeroClass.toAdd.{u4} γ (AddMonoid.toAddZeroClass.{u4} γ (AddCommMonoid.toAddMonoid.{u4} γ _inst_3))) _inst_5))) g) f)) (Summable.{u2, u1} α β _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align summable.map_iff_of_equiv Summable.map_iff_of_equivₓ'. -/
/-- A special case of `summable.map_iff_of_left_inverse` for convenience -/
protected theorem Summable.map_iff_of_equiv [AddCommMonoid γ] [TopologicalSpace γ] {G}
    [AddEquivClass G α γ] (g : G) (hg : Continuous g)
    (hg' : Continuous (AddEquivClass.inv g : γ → α)) : Summable (g ∘ f) ↔ Summable f :=
  Summable.map_iff_of_leftInverse g (g : α ≃+ γ).symm hg hg' (AddEquivClass.left_inv g)
#align summable.map_iff_of_equiv Summable.map_iff_of_equiv

#print HasSum.tendsto_sum_nat /-
/-- If `f : ℕ → α` has sum `a`, then the partial sums `∑_{i=0}^{n-1} f i` converge to `a`. -/
theorem HasSum.tendsto_sum_nat {f : ℕ → α} (h : HasSum f a) :
    Tendsto (fun n : ℕ => ∑ i in range n, f i) atTop (𝓝 a) :=
  h.comp tendsto_finset_range
#align has_sum.tendsto_sum_nat HasSum.tendsto_sum_nat
-/

/- warning: has_sum.unique -> HasSum.unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a₁ : α} {a₂ : α} [_inst_3 : T2Space.{u1} α _inst_2], (HasSum.{u1, u2} α β _inst_1 _inst_2 f a₁) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 f a₂) -> (Eq.{succ u1} α a₁ a₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α} {a₁ : α} {a₂ : α} [_inst_3 : T2Space.{u2} α _inst_2], (HasSum.{u2, u1} α β _inst_1 _inst_2 f a₁) -> (HasSum.{u2, u1} α β _inst_1 _inst_2 f a₂) -> (Eq.{succ u2} α a₁ a₂)
Case conversion may be inaccurate. Consider using '#align has_sum.unique HasSum.uniqueₓ'. -/
theorem HasSum.unique {a₁ a₂ : α} [T2Space α] : HasSum f a₁ → HasSum f a₂ → a₁ = a₂ :=
  tendsto_nhds_unique
#align has_sum.unique HasSum.unique

#print Summable.hasSum_iff_tendsto_nat /-
theorem Summable.hasSum_iff_tendsto_nat [T2Space α] {f : ℕ → α} {a : α} (hf : Summable f) :
    HasSum f a ↔ Tendsto (fun n : ℕ => ∑ i in range n, f i) atTop (𝓝 a) :=
  by
  refine' ⟨fun h => h.tendsto_sum_nat, fun h => _⟩
  rw [tendsto_nhds_unique h hf.has_sum.tendsto_sum_nat]
  exact hf.has_sum
#align summable.has_sum_iff_tendsto_nat Summable.hasSum_iff_tendsto_nat
-/

/- warning: function.surjective.summable_iff_of_has_sum_iff -> Function.Surjective.summable_iff_of_hasSum_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {α' : Type.{u4}} [_inst_3 : AddCommMonoid.{u4} α'] [_inst_4 : TopologicalSpace.{u4} α'] {e : α' -> α}, (Function.Surjective.{succ u4, succ u1} α' α e) -> (forall {f : β -> α} {g : γ -> α'}, (forall {a : α'}, Iff (HasSum.{u1, u2} α β _inst_1 _inst_2 f (e a)) (HasSum.{u4, u3} α' γ _inst_3 _inst_4 g a)) -> (Iff (Summable.{u1, u2} α β _inst_1 _inst_2 f) (Summable.{u4, u3} α' γ _inst_3 _inst_4 g)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : AddCommMonoid.{u3} α] [_inst_2 : TopologicalSpace.{u3} α] {α' : Type.{u4}} [_inst_3 : AddCommMonoid.{u4} α'] [_inst_4 : TopologicalSpace.{u4} α'] {e : α' -> α}, (Function.Surjective.{succ u4, succ u3} α' α e) -> (forall {f : β -> α} {g : γ -> α'}, (forall {a : α'}, Iff (HasSum.{u3, u2} α β _inst_1 _inst_2 f (e a)) (HasSum.{u4, u1} α' γ _inst_3 _inst_4 g a)) -> (Iff (Summable.{u3, u2} α β _inst_1 _inst_2 f) (Summable.{u4, u1} α' γ _inst_3 _inst_4 g)))
Case conversion may be inaccurate. Consider using '#align function.surjective.summable_iff_of_has_sum_iff Function.Surjective.summable_iff_of_hasSum_iffₓ'. -/
theorem Function.Surjective.summable_iff_of_hasSum_iff {α' : Type _} [AddCommMonoid α']
    [TopologicalSpace α'] {e : α' → α} (hes : Function.Surjective e) {f : β → α} {g : γ → α'}
    (he : ∀ {a}, HasSum f (e a) ↔ HasSum g a) : Summable f ↔ Summable g :=
  hes.exists.trans <| exists_congr <| @he
#align function.surjective.summable_iff_of_has_sum_iff Function.Surjective.summable_iff_of_hasSum_iff

variable [ContinuousAdd α]

/- warning: has_sum.add -> HasSum.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {g : β -> α} {a : α} {b : α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))], (HasSum.{u1, u2} α β _inst_1 _inst_2 f a) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 g b) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 (fun (b : β) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (f b) (g b)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α} {g : β -> α} {a : α} {b : α} [_inst_3 : ContinuousAdd.{u2} α _inst_2 (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))], (HasSum.{u2, u1} α β _inst_1 _inst_2 f a) -> (HasSum.{u2, u1} α β _inst_1 _inst_2 g b) -> (HasSum.{u2, u1} α β _inst_1 _inst_2 (fun (b : β) => HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))) (f b) (g b)) (HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))) a b))
Case conversion may be inaccurate. Consider using '#align has_sum.add HasSum.addₓ'. -/
theorem HasSum.add (hf : HasSum f a) (hg : HasSum g b) : HasSum (fun b => f b + g b) (a + b) := by
  simp only [HasSum, sum_add_distrib] <;> exact hf.add hg
#align has_sum.add HasSum.add

/- warning: summable.add -> Summable.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {g : β -> α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))], (Summable.{u1, u2} α β _inst_1 _inst_2 f) -> (Summable.{u1, u2} α β _inst_1 _inst_2 g) -> (Summable.{u1, u2} α β _inst_1 _inst_2 (fun (b : β) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (f b) (g b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α} {g : β -> α} [_inst_3 : ContinuousAdd.{u2} α _inst_2 (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))], (Summable.{u2, u1} α β _inst_1 _inst_2 f) -> (Summable.{u2, u1} α β _inst_1 _inst_2 g) -> (Summable.{u2, u1} α β _inst_1 _inst_2 (fun (b : β) => HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))) (f b) (g b)))
Case conversion may be inaccurate. Consider using '#align summable.add Summable.addₓ'. -/
theorem Summable.add (hf : Summable f) (hg : Summable g) : Summable fun b => f b + g b :=
  (hf.HasSum.add hg.HasSum).Summable
#align summable.add Summable.add

/- warning: has_sum_sum -> hasSum_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {f : γ -> β -> α} {a : γ -> α} {s : Finset.{u3} γ}, (forall (i : γ), (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) i s) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 (f i) (a i))) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 (fun (b : β) => Finset.sum.{u1, u3} α γ _inst_1 s (fun (i : γ) => f i b)) (Finset.sum.{u1, u3} α γ _inst_1 s (fun (i : γ) => a i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : ContinuousAdd.{u2} α _inst_2 (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))] {f : γ -> β -> α} {a : γ -> α} {s : Finset.{u3} γ}, (forall (i : γ), (Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) i s) -> (HasSum.{u2, u1} α β _inst_1 _inst_2 (f i) (a i))) -> (HasSum.{u2, u1} α β _inst_1 _inst_2 (fun (b : β) => Finset.sum.{u2, u3} α γ _inst_1 s (fun (i : γ) => f i b)) (Finset.sum.{u2, u3} α γ _inst_1 s (fun (i : γ) => a i)))
Case conversion may be inaccurate. Consider using '#align has_sum_sum hasSum_sumₓ'. -/
theorem hasSum_sum {f : γ → β → α} {a : γ → α} {s : Finset γ} :
    (∀ i ∈ s, HasSum (f i) (a i)) → HasSum (fun b => ∑ i in s, f i b) (∑ i in s, a i) :=
  Finset.induction_on s (by simp only [hasSum_zero, sum_empty, forall_true_iff])
    (by
      simp (config := { contextual := true }) only [HasSum.add, sum_insert, mem_insert,
        forall_eq_or_imp, forall₂_true_iff, not_false_iff, forall_true_iff])
#align has_sum_sum hasSum_sum

/- warning: summable_sum -> summable_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {f : γ -> β -> α} {s : Finset.{u3} γ}, (forall (i : γ), (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) i s) -> (Summable.{u1, u2} α β _inst_1 _inst_2 (f i))) -> (Summable.{u1, u2} α β _inst_1 _inst_2 (fun (b : β) => Finset.sum.{u1, u3} α γ _inst_1 s (fun (i : γ) => f i b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : ContinuousAdd.{u2} α _inst_2 (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))] {f : γ -> β -> α} {s : Finset.{u3} γ}, (forall (i : γ), (Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) i s) -> (Summable.{u2, u1} α β _inst_1 _inst_2 (f i))) -> (Summable.{u2, u1} α β _inst_1 _inst_2 (fun (b : β) => Finset.sum.{u2, u3} α γ _inst_1 s (fun (i : γ) => f i b)))
Case conversion may be inaccurate. Consider using '#align summable_sum summable_sumₓ'. -/
theorem summable_sum {f : γ → β → α} {s : Finset γ} (hf : ∀ i ∈ s, Summable (f i)) :
    Summable fun b => ∑ i in s, f i b :=
  (hasSum_sum fun i hi => (hf i hi).HasSum).Summable
#align summable_sum summable_sum

/- warning: has_sum.add_disjoint -> HasSum.add_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {b : α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β} {t : Set.{u2} β}, (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) s t) -> (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))))) a) -> (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t))))))) b) -> (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)))))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) a b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {b : α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β} {t : Set.{u2} β}, (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} β) (Preorder.toLE.{u2} (Set.{u2} β) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))) s t) -> (HasSum.{u1, u2} α (Set.Elem.{u2} β s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β s) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s))) a) -> (HasSum.{u1, u2} α (Set.Elem.{u2} β t) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β t) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t))) b) -> (HasSum.{u1, u2} α (Set.Elem.{u2} β (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) a b))
Case conversion may be inaccurate. Consider using '#align has_sum.add_disjoint HasSum.add_disjointₓ'. -/
theorem HasSum.add_disjoint {s t : Set β} (hs : Disjoint s t) (ha : HasSum (f ∘ coe : s → α) a)
    (hb : HasSum (f ∘ coe : t → α) b) : HasSum (f ∘ coe : s ∪ t → α) (a + b) :=
  by
  rw [hasSum_subtype_iff_indicator] at *
  rw [Set.indicator_union_of_disjoint hs]
  exact ha.add hb
#align has_sum.add_disjoint HasSum.add_disjoint

/- warning: has_sum_sum_disjoint -> hasSum_sum_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {ι : Type.{u3}} (s : Finset.{u3} ι) {t : ι -> (Set.{u2} β)} {a : ι -> α}, (Set.Pairwise.{u3} ι ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Finset.{u3} ι) (Set.{u3} ι) (HasLiftT.mk.{succ u3, succ u3} (Finset.{u3} ι) (Set.{u3} ι) (CoeTCₓ.coe.{succ u3, succ u3} (Finset.{u3} ι) (Set.{u3} ι) (Finset.Set.hasCoeT.{u3} ι))) s) (Function.onFun.{succ u3, succ u2, 1} ι (Set.{u2} β) Prop (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))) t)) -> (forall (i : ι), (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) -> (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (t i)))))))) (a i))) -> (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) => t i)))) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) => t i)))) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) => t i)))) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) => t i)))) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) => t i)))) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) => t i)))) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) => t i)))))))))) (Finset.sum.{u1, u3} α ι _inst_1 s (fun (i : ι) => a i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {ι : Type.{u3}} (s : Finset.{u3} ι) {t : ι -> (Set.{u2} β)} {a : ι -> α}, (Set.Pairwise.{u3} ι (Finset.toSet.{u3} ι s) (Function.onFun.{succ u3, succ u2, 1} ι (Set.{u2} β) Prop (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} β) (Preorder.toLE.{u2} (Set.{u2} β) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))))) t)) -> (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) -> (HasSum.{u1, u2} α (Set.Elem.{u2} β (t i)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β (t i)) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (t i)))) (a i))) -> (HasSum.{u1, u2} α (Set.Elem.{u2} β (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) (fun (H : Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) => t i)))) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) (fun (H : Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) => t i)))) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) (fun (h._@.Mathlib.Topology.Algebra.InfiniteSum.Basic._hyg.4330 : Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) => t i)))))) (Finset.sum.{u1, u3} α ι _inst_1 s (fun (i : ι) => a i)))
Case conversion may be inaccurate. Consider using '#align has_sum_sum_disjoint hasSum_sum_disjointₓ'. -/
theorem hasSum_sum_disjoint {ι} (s : Finset ι) {t : ι → Set β} {a : ι → α}
    (hs : (s : Set ι).Pairwise (Disjoint on t)) (hf : ∀ i ∈ s, HasSum (f ∘ coe : t i → α) (a i)) :
    HasSum (f ∘ coe : (⋃ i ∈ s, t i) → α) (∑ i in s, a i) :=
  by
  simp_rw [hasSum_subtype_iff_indicator] at *
  rw [Set.indicator_finset_bunionᵢ _ _ hs]
  exact hasSum_sum hf
#align has_sum_sum_disjoint hasSum_sum_disjoint

/- warning: has_sum.add_is_compl -> HasSum.add_isCompl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {b : α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β} {t : Set.{u2} β}, (IsCompl.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))) s t) -> (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))))) a) -> (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t))))))) b) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) a b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {b : α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β} {t : Set.{u2} β}, (IsCompl.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))) s t) -> (HasSum.{u1, u2} α (Set.Elem.{u2} β s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β s) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s))) a) -> (HasSum.{u1, u2} α (Set.Elem.{u2} β t) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β t) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t))) b) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) a b))
Case conversion may be inaccurate. Consider using '#align has_sum.add_is_compl HasSum.add_isComplₓ'. -/
theorem HasSum.add_isCompl {s t : Set β} (hs : IsCompl s t) (ha : HasSum (f ∘ coe : s → α) a)
    (hb : HasSum (f ∘ coe : t → α) b) : HasSum f (a + b) := by
  simpa [← hs.compl_eq] using
    (hasSum_subtype_iff_indicator.1 ha).add (hasSum_subtype_iff_indicator.1 hb)
#align has_sum.add_is_compl HasSum.add_isCompl

/- warning: has_sum.add_compl -> HasSum.add_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {b : α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β}, (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))))) a) -> (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)))))))) b) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) a b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {b : α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β}, (HasSum.{u1, u2} α (Set.Elem.{u2} β s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β s) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s))) a) -> (HasSum.{u1, u2} α (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)))) b) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) a b))
Case conversion may be inaccurate. Consider using '#align has_sum.add_compl HasSum.add_complₓ'. -/
theorem HasSum.add_compl {s : Set β} (ha : HasSum (f ∘ coe : s → α) a)
    (hb : HasSum (f ∘ coe : sᶜ → α) b) : HasSum f (a + b) :=
  ha.add_isCompl isCompl_compl hb
#align has_sum.add_compl HasSum.add_compl

/- warning: summable.add_compl -> Summable.add_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β}, (Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s)))))))) -> (Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s))))))))) -> (Summable.{u1, u2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β}, (Summable.{u1, u2} α (Set.Elem.{u2} β s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β s) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s)))) -> (Summable.{u1, u2} α (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s))))) -> (Summable.{u1, u2} α β _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align summable.add_compl Summable.add_complₓ'. -/
theorem Summable.add_compl {s : Set β} (hs : Summable (f ∘ coe : s → α))
    (hsc : Summable (f ∘ coe : sᶜ → α)) : Summable f :=
  (hs.HasSum.add_compl hsc.HasSum).Summable
#align summable.add_compl Summable.add_compl

/- warning: has_sum.compl_add -> HasSum.compl_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {b : α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β}, (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)))))))) a) -> (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))))) b) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) a b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α} {b : α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β}, (HasSum.{u1, u2} α (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)))) a) -> (HasSum.{u1, u2} α (Set.Elem.{u2} β s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β s) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s))) b) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) a b))
Case conversion may be inaccurate. Consider using '#align has_sum.compl_add HasSum.compl_addₓ'. -/
theorem HasSum.compl_add {s : Set β} (ha : HasSum (f ∘ coe : sᶜ → α) a)
    (hb : HasSum (f ∘ coe : s → α) b) : HasSum f (a + b) :=
  ha.add_isCompl isCompl_compl.symm hb
#align has_sum.compl_add HasSum.compl_add

/- warning: has_sum.even_add_odd -> HasSum.even_add_odd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {a : α} {b : α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {f : Nat -> α}, (HasSum.{u1, 0} α Nat _inst_1 _inst_2 (fun (k : Nat) => f (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k)) a) -> (HasSum.{u1, 0} α Nat _inst_1 _inst_2 (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) b) -> (HasSum.{u1, 0} α Nat _inst_1 _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {a : α} {b : α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {f : Nat -> α}, (HasSum.{u1, 0} α Nat _inst_1 _inst_2 (fun (k : Nat) => f (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k)) a) -> (HasSum.{u1, 0} α Nat _inst_1 _inst_2 (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) b) -> (HasSum.{u1, 0} α Nat _inst_1 _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) a b))
Case conversion may be inaccurate. Consider using '#align has_sum.even_add_odd HasSum.even_add_oddₓ'. -/
theorem HasSum.even_add_odd {f : ℕ → α} (he : HasSum (fun k => f (2 * k)) a)
    (ho : HasSum (fun k => f (2 * k + 1)) b) : HasSum f (a + b) :=
  by
  have := mul_right_injective₀ (two_ne_zero' ℕ)
  replace he := this.has_sum_range_iff.2 he
  replace ho := ((add_left_injective 1).comp this).hasSum_range_iff.2 ho
  refine' he.add_is_compl _ ho
  simpa [(· ∘ ·)] using Nat.isCompl_even_odd
#align has_sum.even_add_odd HasSum.even_add_odd

/- warning: summable.compl_add -> Summable.compl_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β}, (Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s))))))))) -> (Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s)))))))) -> (Summable.{u1, u2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β}, (Summable.{u1, u2} α (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s))))) -> (Summable.{u1, u2} α (Set.Elem.{u2} β s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β s) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s)))) -> (Summable.{u1, u2} α β _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align summable.compl_add Summable.compl_addₓ'. -/
theorem Summable.compl_add {s : Set β} (hs : Summable (f ∘ coe : sᶜ → α))
    (hsc : Summable (f ∘ coe : s → α)) : Summable f :=
  (hs.HasSum.compl_add hsc.HasSum).Summable
#align summable.compl_add Summable.compl_add

/- warning: summable.even_add_odd -> Summable.even_add_odd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {f : Nat -> α}, (Summable.{u1, 0} α Nat _inst_1 _inst_2 (fun (k : Nat) => f (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k))) -> (Summable.{u1, 0} α Nat _inst_1 _inst_2 (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) -> (Summable.{u1, 0} α Nat _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {f : Nat -> α}, (Summable.{u1, 0} α Nat _inst_1 _inst_2 (fun (k : Nat) => f (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k))) -> (Summable.{u1, 0} α Nat _inst_1 _inst_2 (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) -> (Summable.{u1, 0} α Nat _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align summable.even_add_odd Summable.even_add_oddₓ'. -/
theorem Summable.even_add_odd {f : ℕ → α} (he : Summable fun k => f (2 * k))
    (ho : Summable fun k => f (2 * k + 1)) : Summable f :=
  (he.HasSum.even_add_odd ho.HasSum).Summable
#align summable.even_add_odd Summable.even_add_odd

/- warning: has_sum.sigma -> HasSum.sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] [_inst_4 : RegularSpace.{u1} α _inst_2] {γ : β -> Type.{u3}} {f : (Sigma.{u2, u3} β (fun (b : β) => γ b)) -> α} {g : β -> α} {a : α}, (HasSum.{u1, max u2 u3} α (Sigma.{u2, u3} β (fun (b : β) => γ b)) _inst_1 _inst_2 f a) -> (forall (b : β), HasSum.{u1, u3} α (γ b) _inst_1 _inst_2 (fun (c : γ b) => f (Sigma.mk.{u2, u3} β (fun (b : β) => γ b) b c)) (g b)) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 g a)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u3} α] [_inst_2 : TopologicalSpace.{u3} α] [_inst_3 : ContinuousAdd.{u3} α _inst_2 (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1)))] [_inst_4 : RegularSpace.{u3} α _inst_2] {γ : β -> Type.{u2}} {f : (Sigma.{u1, u2} β (fun (b : β) => γ b)) -> α} {g : β -> α} {a : α}, (HasSum.{u3, max u1 u2} α (Sigma.{u1, u2} β (fun (b : β) => γ b)) _inst_1 _inst_2 f a) -> (forall (b : β), HasSum.{u3, u2} α (γ b) _inst_1 _inst_2 (fun (c : γ b) => f (Sigma.mk.{u1, u2} β (fun (b : β) => γ b) b c)) (g b)) -> (HasSum.{u3, u1} α β _inst_1 _inst_2 g a)
Case conversion may be inaccurate. Consider using '#align has_sum.sigma HasSum.sigmaₓ'. -/
theorem HasSum.sigma [RegularSpace α] {γ : β → Type _} {f : (Σb : β, γ b) → α} {g : β → α} {a : α}
    (ha : HasSum f a) (hf : ∀ b, HasSum (fun c => f ⟨b, c⟩) (g b)) : HasSum g a :=
  by
  refine' (at_top_basis.tendsto_iff (closed_nhds_basis a)).mpr _
  rintro s ⟨hs, hsc⟩
  rcases mem_at_top_sets.mp (ha hs) with ⟨u, hu⟩
  use u.image Sigma.fst, trivial
  intro bs hbs
  simp only [Set.mem_preimage, ge_iff_le, Finset.le_iff_subset] at hu
  have :
    tendsto (fun t : Finset (Σb, γ b) => ∑ p in t.filterₓ fun p => p.1 ∈ bs, f p) at_top
      (𝓝 <| ∑ b in bs, g b) :=
    by
    simp only [← sigma_preimage_mk, sum_sigma]
    refine' tendsto_finset_sum _ fun b hb => _
    change
      tendsto (fun t => (fun t => ∑ s in t, f ⟨b, s⟩) (preimage t (Sigma.mk b) _)) at_top (𝓝 (g b))
    exact tendsto.comp (hf b) (tendsto_finset_preimage_at_top_at_top _)
  refine' hsc.mem_of_tendsto this (eventually_at_top.2 ⟨u, fun t ht => hu _ fun x hx => _⟩)
  exact mem_filter.2 ⟨ht hx, hbs <| mem_image_of_mem _ hx⟩
#align has_sum.sigma HasSum.sigma

/- warning: has_sum.prod_fiberwise -> HasSum.prod_fiberwise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] [_inst_4 : RegularSpace.{u1} α _inst_2] {f : (Prod.{u2, u3} β γ) -> α} {g : β -> α} {a : α}, (HasSum.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 _inst_2 f a) -> (forall (b : β), HasSum.{u1, u3} α γ _inst_1 _inst_2 (fun (c : γ) => f (Prod.mk.{u2, u3} β γ b c)) (g b)) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 g a)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : AddCommMonoid.{u3} α] [_inst_2 : TopologicalSpace.{u3} α] [_inst_3 : ContinuousAdd.{u3} α _inst_2 (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1)))] [_inst_4 : RegularSpace.{u3} α _inst_2] {f : (Prod.{u2, u1} β γ) -> α} {g : β -> α} {a : α}, (HasSum.{u3, max u2 u1} α (Prod.{u2, u1} β γ) _inst_1 _inst_2 f a) -> (forall (b : β), HasSum.{u3, u1} α γ _inst_1 _inst_2 (fun (c : γ) => f (Prod.mk.{u2, u1} β γ b c)) (g b)) -> (HasSum.{u3, u2} α β _inst_1 _inst_2 g a)
Case conversion may be inaccurate. Consider using '#align has_sum.prod_fiberwise HasSum.prod_fiberwiseₓ'. -/
/-- If a series `f` on `β × γ` has sum `a` and for each `b` the restriction of `f` to `{b} × γ`
has sum `g b`, then the series `g` has sum `a`. -/
theorem HasSum.prod_fiberwise [RegularSpace α] {f : β × γ → α} {g : β → α} {a : α} (ha : HasSum f a)
    (hf : ∀ b, HasSum (fun c => f (b, c)) (g b)) : HasSum g a :=
  HasSum.sigma ((Equiv.sigmaEquivProd β γ).hasSum_iff.2 ha) hf
#align has_sum.prod_fiberwise HasSum.prod_fiberwise

/- warning: summable.sigma' -> Summable.sigma' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] [_inst_4 : RegularSpace.{u1} α _inst_2] {γ : β -> Type.{u3}} {f : (Sigma.{u2, u3} β (fun (b : β) => γ b)) -> α}, (Summable.{u1, max u2 u3} α (Sigma.{u2, u3} β (fun (b : β) => γ b)) _inst_1 _inst_2 f) -> (forall (b : β), Summable.{u1, u3} α (γ b) _inst_1 _inst_2 (fun (c : γ b) => f (Sigma.mk.{u2, u3} β (fun (b : β) => γ b) b c))) -> (Summable.{u1, u2} α β _inst_1 _inst_2 (fun (b : β) => tsum.{u1, u3} α _inst_1 _inst_2 (γ b) (fun (c : γ b) => f (Sigma.mk.{u2, u3} β (fun (b : β) => γ b) b c))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u3} α] [_inst_2 : TopologicalSpace.{u3} α] [_inst_3 : ContinuousAdd.{u3} α _inst_2 (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1)))] [_inst_4 : RegularSpace.{u3} α _inst_2] {γ : β -> Type.{u2}} {f : (Sigma.{u1, u2} β (fun (b : β) => γ b)) -> α}, (Summable.{u3, max u1 u2} α (Sigma.{u1, u2} β (fun (b : β) => γ b)) _inst_1 _inst_2 f) -> (forall (b : β), Summable.{u3, u2} α (γ b) _inst_1 _inst_2 (fun (c : γ b) => f (Sigma.mk.{u1, u2} β (fun (b : β) => γ b) b c))) -> (Summable.{u3, u1} α β _inst_1 _inst_2 (fun (b : β) => tsum.{u3, u2} α _inst_1 _inst_2 (γ b) (fun (c : γ b) => f (Sigma.mk.{u1, u2} β (fun (b : β) => γ b) b c))))
Case conversion may be inaccurate. Consider using '#align summable.sigma' Summable.sigma'ₓ'. -/
theorem Summable.sigma' [RegularSpace α] {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f)
    (hf : ∀ b, Summable fun c => f ⟨b, c⟩) : Summable fun b => ∑' c, f ⟨b, c⟩ :=
  (ha.HasSum.Sigma fun b => (hf b).HasSum).Summable
#align summable.sigma' Summable.sigma'

/- warning: has_sum.sigma_of_has_sum -> HasSum.sigma_of_hasSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] [_inst_4 : T3Space.{u1} α _inst_2] {γ : β -> Type.{u3}} {f : (Sigma.{u2, u3} β (fun (b : β) => γ b)) -> α} {g : β -> α} {a : α}, (HasSum.{u1, u2} α β _inst_1 _inst_2 g a) -> (forall (b : β), HasSum.{u1, u3} α (γ b) _inst_1 _inst_2 (fun (c : γ b) => f (Sigma.mk.{u2, u3} β (fun (b : β) => γ b) b c)) (g b)) -> (Summable.{u1, max u2 u3} α (Sigma.{u2, u3} β (fun (b : β) => γ b)) _inst_1 _inst_2 f) -> (HasSum.{u1, max u2 u3} α (Sigma.{u2, u3} β (fun (b : β) => γ b)) _inst_1 _inst_2 f a)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u3} α] [_inst_2 : TopologicalSpace.{u3} α] [_inst_3 : ContinuousAdd.{u3} α _inst_2 (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1)))] [_inst_4 : T3Space.{u3} α _inst_2] {γ : β -> Type.{u2}} {f : (Sigma.{u1, u2} β (fun (b : β) => γ b)) -> α} {g : β -> α} {a : α}, (HasSum.{u3, u1} α β _inst_1 _inst_2 g a) -> (forall (b : β), HasSum.{u3, u2} α (γ b) _inst_1 _inst_2 (fun (c : γ b) => f (Sigma.mk.{u1, u2} β (fun (b : β) => γ b) b c)) (g b)) -> (Summable.{u3, max u1 u2} α (Sigma.{u1, u2} β (fun (b : β) => γ b)) _inst_1 _inst_2 f) -> (HasSum.{u3, max u1 u2} α (Sigma.{u1, u2} β (fun (b : β) => γ b)) _inst_1 _inst_2 f a)
Case conversion may be inaccurate. Consider using '#align has_sum.sigma_of_has_sum HasSum.sigma_of_hasSumₓ'. -/
theorem HasSum.sigma_of_hasSum [T3Space α] {γ : β → Type _} {f : (Σb : β, γ b) → α} {g : β → α}
    {a : α} (ha : HasSum g a) (hf : ∀ b, HasSum (fun c => f ⟨b, c⟩) (g b)) (hf' : Summable f) :
    HasSum f a := by simpa [(hf'.has_sum.sigma hf).unique ha] using hf'.has_sum
#align has_sum.sigma_of_has_sum HasSum.sigma_of_hasSum

/- warning: has_sum.update' -> HasSum.update' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : TopologicalSpace.{u1} α] [_inst_5 : AddCommMonoid.{u1} α] [_inst_6 : T2Space.{u1} α _inst_4] [_inst_7 : ContinuousAdd.{u1} α _inst_4 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5)))] {f : β -> α} {a : α} {a' : α}, (HasSum.{u1, u2} α β _inst_5 _inst_4 f a) -> (forall (b : β) (x : α), (HasSum.{u1, u2} α β _inst_5 _inst_4 (Function.update.{succ u2, succ u1} β (fun (ᾰ : β) => α) (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u2} β a b)) f b x) a') -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5)))) a x) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5)))) a' (f b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : TopologicalSpace.{u2} α] [_inst_5 : AddCommMonoid.{u2} α] [_inst_6 : T2Space.{u2} α _inst_4] [_inst_7 : ContinuousAdd.{u2} α _inst_4 (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_5)))] {f : β -> α} {a : α} {a' : α}, (HasSum.{u2, u1} α β _inst_5 _inst_4 f a) -> (forall (b : β) (x : α), (HasSum.{u2, u1} α β _inst_5 _inst_4 (Function.update.{succ u1, succ u2} β (fun (ᾰ : β) => α) (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u1} β a b)) f b x) a') -> (Eq.{succ u2} α (HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_5)))) a x) (HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_5)))) a' (f b))))
Case conversion may be inaccurate. Consider using '#align has_sum.update' HasSum.update'ₓ'. -/
/-- Version of `has_sum.update` for `add_comm_monoid` rather than `add_comm_group`.
Rather than showing that `f.update` has a specific sum in terms of `has_sum`,
it gives a relationship between the sums of `f` and `f.update` given that both exist. -/
theorem HasSum.update' {α β : Type _} [TopologicalSpace α] [AddCommMonoid α] [T2Space α]
    [ContinuousAdd α] {f : β → α} {a a' : α} (hf : HasSum f a) (b : β) (x : α)
    (hf' : HasSum (f.update b x) a') : a + x = a' + f b :=
  by
  have : ∀ b', f b' + ite (b' = b) x 0 = f.update b x b' + ite (b' = b) (f b) 0 :=
    by
    intro b'
    split_ifs with hb'
    · simpa only [Function.update_apply, hb', eq_self_iff_true] using add_comm (f b) x
    · simp only [Function.update_apply, hb', if_false]
  have h := hf.add (hasSum_ite_eq b x)
  simp_rw [this] at h
  exact HasSum.unique h (hf'.add (hasSum_ite_eq b (f b)))
#align has_sum.update' HasSum.update'

/- warning: eq_add_of_has_sum_ite -> eq_add_of_hasSum_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : TopologicalSpace.{u1} α] [_inst_5 : AddCommMonoid.{u1} α] [_inst_6 : T2Space.{u1} α _inst_4] [_inst_7 : ContinuousAdd.{u1} α _inst_4 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5)))] {f : β -> α} {a : α}, (HasSum.{u1, u2} α β _inst_5 _inst_4 f a) -> (forall (b : β) (a' : α), (HasSum.{u1, u2} α β _inst_5 _inst_4 (fun (n : β) => ite.{succ u1} α (Eq.{succ u2} β n b) (Classical.propDecidable (Eq.{succ u2} β n b)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5)))))) (f n)) a') -> (Eq.{succ u1} α a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5)))) a' (f b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : TopologicalSpace.{u2} α] [_inst_5 : AddCommMonoid.{u2} α] [_inst_6 : T2Space.{u2} α _inst_4] [_inst_7 : ContinuousAdd.{u2} α _inst_4 (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_5)))] {f : β -> α} {a : α}, (HasSum.{u2, u1} α β _inst_5 _inst_4 f a) -> (forall (b : β) (a' : α), (HasSum.{u2, u1} α β _inst_5 _inst_4 (fun (n : β) => ite.{succ u2} α (Eq.{succ u1} β n b) (Classical.propDecidable (Eq.{succ u1} β n b)) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_5)))) (f n)) a') -> (Eq.{succ u2} α a (HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_5)))) a' (f b))))
Case conversion may be inaccurate. Consider using '#align eq_add_of_has_sum_ite eq_add_of_hasSum_iteₓ'. -/
/-- Version of `has_sum_ite_sub_has_sum` for `add_comm_monoid` rather than `add_comm_group`.
Rather than showing that the `ite` expression has a specific sum in terms of `has_sum`,
it gives a relationship between the sums of `f` and `ite (n = b) 0 (f n)` given that both exist. -/
theorem eq_add_of_hasSum_ite {α β : Type _} [TopologicalSpace α] [AddCommMonoid α] [T2Space α]
    [ContinuousAdd α] {f : β → α} {a : α} (hf : HasSum f a) (b : β) (a' : α)
    (hf' : HasSum (fun n => ite (n = b) 0 (f n)) a') : a = a' + f b :=
  by
  refine' (add_zero a).symm.trans (hf.update' b 0 _)
  convert hf'
  exact funext (f.update_apply b 0)
#align eq_add_of_has_sum_ite eq_add_of_hasSum_ite

end HasSum

section tsum

variable [AddCommMonoid α] [TopologicalSpace α]

#print tsum_congr_subtype /-
theorem tsum_congr_subtype (f : β → α) {s t : Set β} (h : s = t) :
    (∑' x : s, f x) = ∑' x : t, f x := by rw [h]
#align tsum_congr_subtype tsum_congr_subtype
-/

/- warning: tsum_zero' -> tsum_zero' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α], (IsClosed.{u1} α _inst_2 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α], (IsClosed.{u2} α _inst_2 (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))))) -> (Eq.{succ u2} α (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align tsum_zero' tsum_zero'ₓ'. -/
theorem tsum_zero' (hz : IsClosed ({0} : Set α)) : (∑' b : β, (0 : α)) = 0 := by
  classical
    rw [tsum, dif_pos summable_zero]
    suffices ∀ x : α, HasSum (fun b : β => (0 : α)) x → x = 0 by
      exact this _ (Classical.choose_spec _)
    intro x hx
    contrapose! hx
    simp only [HasSum, tendsto_nhds, Finset.sum_const_zero, Filter.mem_atTop_sets, ge_iff_le,
      Finset.le_eq_subset, Set.mem_preimage, not_forall, not_exists, exists_prop, exists_and_right]
    refine' ⟨{0}ᶜ, ⟨is_open_compl_iff.mpr hz, _⟩, fun y => ⟨⟨y, subset_refl _⟩, _⟩⟩
    · simpa using hx
    · simp
#align tsum_zero' tsum_zero'

/- warning: tsum_zero -> tsum_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T1Space.{u1} α _inst_2], Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T1Space.{u2} α _inst_2], Eq.{succ u2} α (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align tsum_zero tsum_zeroₓ'. -/
@[simp]
theorem tsum_zero [T1Space α] : (∑' b : β, (0 : α)) = 0 :=
  tsum_zero' isClosed_singleton
#align tsum_zero tsum_zero

variable [T2Space α] {f g : β → α} {a a₁ a₂ : α}

/- warning: has_sum.tsum_eq -> HasSum.tsum_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} {a : α}, (HasSum.{u1, u2} α β _inst_1 _inst_2 f a) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => f b)) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] {f : β -> α} {a : α}, (HasSum.{u2, u1} α β _inst_1 _inst_2 f a) -> (Eq.{succ u2} α (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => f b)) a)
Case conversion may be inaccurate. Consider using '#align has_sum.tsum_eq HasSum.tsum_eqₓ'. -/
theorem HasSum.tsum_eq (ha : HasSum f a) : (∑' b, f b) = a :=
  (Summable.hasSum ⟨a, ha⟩).unique ha
#align has_sum.tsum_eq HasSum.tsum_eq

/- warning: summable.has_sum_iff -> Summable.hasSum_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} {a : α}, (Summable.{u1, u2} α β _inst_1 _inst_2 f) -> (Iff (HasSum.{u1, u2} α β _inst_1 _inst_2 f a) (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => f b)) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] {f : β -> α} {a : α}, (Summable.{u2, u1} α β _inst_1 _inst_2 f) -> (Iff (HasSum.{u2, u1} α β _inst_1 _inst_2 f a) (Eq.{succ u2} α (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => f b)) a))
Case conversion may be inaccurate. Consider using '#align summable.has_sum_iff Summable.hasSum_iffₓ'. -/
theorem Summable.hasSum_iff (h : Summable f) : HasSum f a ↔ (∑' b, f b) = a :=
  Iff.intro HasSum.tsum_eq fun eq => Eq ▸ h.HasSum
#align summable.has_sum_iff Summable.hasSum_iff

/- warning: tsum_empty -> tsum_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} [_inst_4 : IsEmpty.{succ u2} β], Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => f b)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} [_inst_4 : IsEmpty.{succ u2} β], Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => f b)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align tsum_empty tsum_emptyₓ'. -/
@[simp]
theorem tsum_empty [IsEmpty β] : (∑' b, f b) = 0 :=
  hasSum_empty.tsum_eq
#align tsum_empty tsum_empty

/- warning: tsum_eq_sum -> tsum_eq_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} {s : Finset.{u2} β}, (forall (b : β), (Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s)) -> (Eq.{succ u1} α (f b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => f b)) (Finset.sum.{u1, u2} α β _inst_1 s (fun (b : β) => f b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} {s : Finset.{u2} β}, (forall (b : β), (Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s)) -> (Eq.{succ u1} α (f b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => f b)) (Finset.sum.{u1, u2} α β _inst_1 s (fun (b : β) => f b)))
Case conversion may be inaccurate. Consider using '#align tsum_eq_sum tsum_eq_sumₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (b «expr ∉ » s) -/
theorem tsum_eq_sum {f : β → α} {s : Finset β} (hf : ∀ (b) (_ : b ∉ s), f b = 0) :
    (∑' b, f b) = ∑ b in s, f b :=
  (hasSum_sum_of_ne_finset_zero hf).tsum_eq
#align tsum_eq_sum tsum_eq_sum

/- warning: sum_eq_tsum_indicator -> sum_eq_tsum_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] (f : β -> α) (s : Finset.{u2} β), Eq.{succ u1} α (Finset.sum.{u1, u2} α β _inst_1 s (fun (x : β) => f x)) (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (x : β) => Set.indicator.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s) f x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] (f : β -> α) (s : Finset.{u2} β), Eq.{succ u1} α (Finset.sum.{u1, u2} α β _inst_1 s (fun (x : β) => f x)) (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (x : β) => Set.indicator.{u2, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (Finset.toSet.{u2} β s) f x))
Case conversion may be inaccurate. Consider using '#align sum_eq_tsum_indicator sum_eq_tsum_indicatorₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ∉ » s) -/
theorem sum_eq_tsum_indicator (f : β → α) (s : Finset β) :
    (∑ x in s, f x) = ∑' x, Set.indicator (↑s) f x :=
  have : ∀ (x) (_ : x ∉ s), Set.indicator (↑s) f x = 0 := fun x hx =>
    Set.indicator_apply_eq_zero.2 fun hx' => (hx <| Finset.mem_coe.1 hx').elim
  (Finset.sum_congr rfl fun x hx =>
        (Set.indicator_apply_eq_self.2 fun hx' => (hx' <| Finset.mem_coe.2 hx).elim).symm).trans
    (tsum_eq_sum this).symm
#align sum_eq_tsum_indicator sum_eq_tsum_indicator

/- warning: tsum_congr -> tsum_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : AddCommMonoid.{u1} α] [_inst_5 : TopologicalSpace.{u1} α] {f : β -> α} {g : β -> α}, (forall (b : β), Eq.{succ u1} α (f b) (g b)) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_4 _inst_5 β (fun (b : β) => f b)) (tsum.{u1, u2} α _inst_4 _inst_5 β (fun (b : β) => g b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : AddCommMonoid.{u2} α] [_inst_5 : TopologicalSpace.{u2} α] {f : β -> α} {g : β -> α}, (forall (b : β), Eq.{succ u2} α (f b) (g b)) -> (Eq.{succ u2} α (tsum.{u2, u1} α _inst_4 _inst_5 β (fun (b : β) => f b)) (tsum.{u2, u1} α _inst_4 _inst_5 β (fun (b : β) => g b)))
Case conversion may be inaccurate. Consider using '#align tsum_congr tsum_congrₓ'. -/
theorem tsum_congr {α β : Type _} [AddCommMonoid α] [TopologicalSpace α] {f g : β → α}
    (hfg : ∀ b, f b = g b) : (∑' b, f b) = ∑' b, g b :=
  congr_arg tsum (funext hfg)
#align tsum_congr tsum_congr

#print tsum_fintype /-
theorem tsum_fintype [Fintype β] (f : β → α) : (∑' b, f b) = ∑ b, f b :=
  (hasSum_fintype f).tsum_eq
#align tsum_fintype tsum_fintype
-/

/- warning: tsum_bool -> tsum_bool is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] (f : Bool -> α), Eq.{succ u1} α (tsum.{u1, 0} α _inst_1 _inst_2 Bool (fun (i : Bool) => f i)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (f (Decidable.decide False Decidable.false)) (f (Decidable.decide True Decidable.true)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] (f : Bool -> α), Eq.{succ u1} α (tsum.{u1, 0} α _inst_1 _inst_2 Bool (fun (i : Bool) => f i)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (f (Decidable.decide False instDecidableFalse)) (f (Decidable.decide True instDecidableTrue)))
Case conversion may be inaccurate. Consider using '#align tsum_bool tsum_boolₓ'. -/
theorem tsum_bool (f : Bool → α) : (∑' i : Bool, f i) = f False + f True := by
  rw [tsum_fintype, Finset.sum_eq_add] <;> simp
#align tsum_bool tsum_bool

/- warning: tsum_eq_single -> tsum_eq_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} (b : β), (forall (b' : β), (Ne.{succ u2} β b' b) -> (Eq.{succ u1} α (f b') (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => f b)) (f b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} (b : β), (forall (b' : β), (Ne.{succ u2} β b' b) -> (Eq.{succ u1} α (f b') (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => f b)) (f b))
Case conversion may be inaccurate. Consider using '#align tsum_eq_single tsum_eq_singleₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (b' «expr ≠ » b) -/
theorem tsum_eq_single {f : β → α} (b : β) (hf : ∀ (b') (_ : b' ≠ b), f b' = 0) :
    (∑' b, f b) = f b :=
  (hasSum_single b hf).tsum_eq
#align tsum_eq_single tsum_eq_single

/- warning: tsum_tsum_eq_single -> tsum_tsum_eq_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] (f : β -> γ -> α) (b : β) (c : γ), (forall (b' : β), (Ne.{succ u2} β b' b) -> (Eq.{succ u1} α (f b' c) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))) -> (forall (b' : β) (c' : γ), (Ne.{succ u3} γ c' c) -> (Eq.{succ u1} α (f b' c') (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b' : β) => tsum.{u1, u3} α _inst_1 _inst_2 γ (fun (c' : γ) => f b' c'))) (f b c))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] (f : β -> γ -> α) (b : β) (c : γ), (forall (b' : β), (Ne.{succ u3} β b' b) -> (Eq.{succ u2} α (f b' c) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))))) -> (forall (b' : β) (c' : γ), (Ne.{succ u1} γ c' c) -> (Eq.{succ u2} α (f b' c') (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))))) -> (Eq.{succ u2} α (tsum.{u2, u3} α _inst_1 _inst_2 β (fun (b' : β) => tsum.{u2, u1} α _inst_1 _inst_2 γ (fun (c' : γ) => f b' c'))) (f b c))
Case conversion may be inaccurate. Consider using '#align tsum_tsum_eq_single tsum_tsum_eq_singleₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b' c') -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (b' «expr ≠ » b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b' c') -/
theorem tsum_tsum_eq_single (f : β → γ → α) (b : β) (c : γ) (hfb : ∀ (b') (_ : b' ≠ b), f b' c = 0)
    (hfc : ∀ (b' : β) (c' : γ), c' ≠ c → f b' c' = 0) : (∑' (b') (c'), f b' c') = f b c :=
  calc
    (∑' (b') (c'), f b' c') = ∑' b', f b' c := tsum_congr fun b' => tsum_eq_single _ (hfc b')
    _ = f b c := tsum_eq_single _ hfb
    
#align tsum_tsum_eq_single tsum_tsum_eq_single

/- warning: tsum_ite_eq -> tsum_ite_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] (b : β) [_inst_4 : DecidablePred.{succ u2} β (fun (_x : β) => Eq.{succ u2} β _x b)] (a : α), Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b' : β) => ite.{succ u1} α (Eq.{succ u2} β b' b) (_inst_4 b') a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))) a
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] (b : β) [_inst_4 : DecidablePred.{succ u2} β (fun (_x : β) => Eq.{succ u2} β _x b)] (a : α), Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b' : β) => ite.{succ u1} α (Eq.{succ u2} β b' b) (_inst_4 b') a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))) a
Case conversion may be inaccurate. Consider using '#align tsum_ite_eq tsum_ite_eqₓ'. -/
@[simp]
theorem tsum_ite_eq (b : β) [DecidablePred (· = b)] (a : α) :
    (∑' b', if b' = b then a else 0) = a :=
  (hasSum_ite_eq b a).tsum_eq
#align tsum_ite_eq tsum_ite_eq

/- warning: tsum_pi_single -> tsum_pi_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] [_inst_4 : DecidableEq.{succ u2} β] (b : β) (a : α), Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b' : β) => Pi.single.{u2, u1} β (fun (b : β) => α) (fun (a : β) (b : β) => _inst_4 a b) (fun (i : β) => AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) b a b')) a
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] [_inst_4 : DecidableEq.{succ u2} β] (b : β) (a : α), Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b' : β) => Pi.single.{u2, u1} β (fun (b : β) => α) (fun (a : β) (b : β) => _inst_4 a b) (fun (i : β) => AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) b a b')) a
Case conversion may be inaccurate. Consider using '#align tsum_pi_single tsum_pi_singleₓ'. -/
@[simp]
theorem tsum_pi_single [DecidableEq β] (b : β) (a : α) : (∑' b', Pi.single b a b') = a :=
  (hasSum_pi_single b a).tsum_eq
#align tsum_pi_single tsum_pi_single

/- warning: tsum_dite_right -> tsum_dite_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] (P : Prop) [_inst_4 : Decidable P] (x : β -> (Not P) -> α), Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => dite.{succ u1} α P _inst_4 (fun (h : P) => OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))) (fun (h : Not P) => x b h))) (dite.{succ u1} α P _inst_4 (fun (h : P) => OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))) (fun (h : Not P) => tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => x b h)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] (P : Prop) [_inst_4 : Decidable P] (x : β -> (Not P) -> α), Eq.{succ u2} α (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => dite.{succ u2} α P _inst_4 (fun (h : P) => OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))) (fun (h : Not P) => x b h))) (dite.{succ u2} α P _inst_4 (fun (h : P) => OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))) (fun (h : Not P) => tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => x b h)))
Case conversion may be inaccurate. Consider using '#align tsum_dite_right tsum_dite_rightₓ'. -/
theorem tsum_dite_right (P : Prop) [Decidable P] (x : β → ¬P → α) :
    (∑' b : β, if h : P then (0 : α) else x b h) = if h : P then (0 : α) else ∑' b : β, x b h := by
  by_cases hP : P <;> simp [hP]
#align tsum_dite_right tsum_dite_right

/- warning: tsum_dite_left -> tsum_dite_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] (P : Prop) [_inst_4 : Decidable P] (x : β -> P -> α), Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => dite.{succ u1} α P _inst_4 (fun (h : P) => x b h) (fun (h : Not P) => OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))) (dite.{succ u1} α P _inst_4 (fun (h : P) => tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => x b h)) (fun (h : Not P) => OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] (P : Prop) [_inst_4 : Decidable P] (x : β -> P -> α), Eq.{succ u2} α (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => dite.{succ u2} α P _inst_4 (fun (h : P) => x b h) (fun (h : Not P) => OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))))) (dite.{succ u2} α P _inst_4 (fun (h : P) => tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => x b h)) (fun (h : Not P) => OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align tsum_dite_left tsum_dite_leftₓ'. -/
theorem tsum_dite_left (P : Prop) [Decidable P] (x : β → P → α) :
    (∑' b : β, if h : P then x b h else 0) = if h : P then ∑' b : β, x b h else 0 := by
  by_cases hP : P <;> simp [hP]
#align tsum_dite_left tsum_dite_left

/- warning: function.surjective.tsum_eq_tsum_of_has_sum_iff_has_sum -> Function.Surjective.tsum_eq_tsum_of_hasSum_iff_hasSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {α' : Type.{u4}} [_inst_4 : AddCommMonoid.{u4} α'] [_inst_5 : TopologicalSpace.{u4} α'] {e : α' -> α}, (Function.Surjective.{succ u4, succ u1} α' α e) -> (Eq.{succ u1} α (e (OfNat.ofNat.{u4} α' 0 (OfNat.mk.{u4} α' 0 (Zero.zero.{u4} α' (AddZeroClass.toHasZero.{u4} α' (AddMonoid.toAddZeroClass.{u4} α' (AddCommMonoid.toAddMonoid.{u4} α' _inst_4))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))))) -> (forall {f : β -> α} {g : γ -> α'}, (forall {a : α'}, Iff (HasSum.{u1, u2} α β _inst_1 _inst_2 f (e a)) (HasSum.{u4, u3} α' γ _inst_4 _inst_5 g a)) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => f b)) (e (tsum.{u4, u3} α' _inst_4 _inst_5 γ (fun (c : γ) => g c)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : AddCommMonoid.{u3} α] [_inst_2 : TopologicalSpace.{u3} α] [_inst_3 : T2Space.{u3} α _inst_2] {α' : Type.{u4}} [_inst_4 : AddCommMonoid.{u4} α'] [_inst_5 : TopologicalSpace.{u4} α'] {e : α' -> α}, (Function.Surjective.{succ u4, succ u3} α' α e) -> (Eq.{succ u3} α (e (OfNat.ofNat.{u4} α' 0 (Zero.toOfNat0.{u4} α' (AddMonoid.toZero.{u4} α' (AddCommMonoid.toAddMonoid.{u4} α' _inst_4))))) (OfNat.ofNat.{u3} α 0 (Zero.toOfNat0.{u3} α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1))))) -> (forall {f : β -> α} {g : γ -> α'}, (forall {a : α'}, Iff (HasSum.{u3, u2} α β _inst_1 _inst_2 f (e a)) (HasSum.{u4, u1} α' γ _inst_4 _inst_5 g a)) -> (Eq.{succ u3} α (tsum.{u3, u2} α _inst_1 _inst_2 β (fun (b : β) => f b)) (e (tsum.{u4, u1} α' _inst_4 _inst_5 γ (fun (c : γ) => g c)))))
Case conversion may be inaccurate. Consider using '#align function.surjective.tsum_eq_tsum_of_has_sum_iff_has_sum Function.Surjective.tsum_eq_tsum_of_hasSum_iff_hasSumₓ'. -/
theorem Function.Surjective.tsum_eq_tsum_of_hasSum_iff_hasSum {α' : Type _} [AddCommMonoid α']
    [TopologicalSpace α'] {e : α' → α} (hes : Function.Surjective e) (h0 : e 0 = 0) {f : β → α}
    {g : γ → α'} (h : ∀ {a}, HasSum f (e a) ↔ HasSum g a) : (∑' b, f b) = e (∑' c, g c) :=
  by_cases (fun this : Summable g => (h.mpr this.HasSum).tsum_eq) fun hg : ¬Summable g =>
    by
    have hf : ¬Summable f := mt (hes.summable_iff_of_hasSum_iff @h).1 hg
    simp [tsum, hf, hg, h0]
#align function.surjective.tsum_eq_tsum_of_has_sum_iff_has_sum Function.Surjective.tsum_eq_tsum_of_hasSum_iff_hasSum

/- warning: tsum_eq_tsum_of_has_sum_iff_has_sum -> tsum_eq_tsum_of_hasSum_iff_hasSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} {g : γ -> α}, (forall {a : α}, Iff (HasSum.{u1, u2} α β _inst_1 _inst_2 f a) (HasSum.{u1, u3} α γ _inst_1 _inst_2 g a)) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => f b)) (tsum.{u1, u3} α _inst_1 _inst_2 γ (fun (c : γ) => g c)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : AddCommMonoid.{u3} α] [_inst_2 : TopologicalSpace.{u3} α] [_inst_3 : T2Space.{u3} α _inst_2] {f : β -> α} {g : γ -> α}, (forall {a : α}, Iff (HasSum.{u3, u2} α β _inst_1 _inst_2 f a) (HasSum.{u3, u1} α γ _inst_1 _inst_2 g a)) -> (Eq.{succ u3} α (tsum.{u3, u2} α _inst_1 _inst_2 β (fun (b : β) => f b)) (tsum.{u3, u1} α _inst_1 _inst_2 γ (fun (c : γ) => g c)))
Case conversion may be inaccurate. Consider using '#align tsum_eq_tsum_of_has_sum_iff_has_sum tsum_eq_tsum_of_hasSum_iff_hasSumₓ'. -/
theorem tsum_eq_tsum_of_hasSum_iff_hasSum {f : β → α} {g : γ → α}
    (h : ∀ {a}, HasSum f a ↔ HasSum g a) : (∑' b, f b) = ∑' c, g c :=
  surjective_id.tsum_eq_tsum_of_hasSum_iff_hasSum rfl @h
#align tsum_eq_tsum_of_has_sum_iff_has_sum tsum_eq_tsum_of_hasSum_iff_hasSum

#print Equiv.tsum_eq /-
theorem Equiv.tsum_eq (j : γ ≃ β) (f : β → α) : (∑' c, f (j c)) = ∑' b, f b :=
  tsum_eq_tsum_of_hasSum_iff_hasSum fun a => j.hasSum_iff
#align equiv.tsum_eq Equiv.tsum_eq
-/

/- warning: equiv.tsum_eq_tsum_of_support -> Equiv.tsum_eq_tsum_of_support is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} {g : γ -> α} (e : Equiv.{succ u2, succ u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g))), (forall (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)), Eq.{succ u1} α (g ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)))))) (coeFn.{max 1 (max (succ u2) (succ u3)) (succ u3) (succ u2), max (succ u2) (succ u3)} (Equiv.{succ u2, succ u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g))) (fun (_x : Equiv.{succ u2, succ u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g))) => (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) -> (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g))) (Equiv.hasCoeToFun.{succ u2, succ u3} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g))) e x))) (f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f)))))) x))) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (x : β) => f x)) (tsum.{u1, u3} α _inst_1 _inst_2 γ (fun (y : γ) => g y)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} {g : γ -> α} (e : Equiv.{succ u3, succ u2} (Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) (Set.Elem.{u2} γ (Function.support.{u2, u1} γ α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) g))), (forall (x : Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)), Eq.{succ u1} α (g (Subtype.val.{succ u2} γ (fun (x : γ) => Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) x (Function.support.{u2, u1} γ α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) g)) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Equiv.{succ u3, succ u2} (Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) (Set.Elem.{u2} γ (Function.support.{u2, u1} γ α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) g))) (Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) (fun (_x : Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) => Set.Elem.{u2} γ (Function.support.{u2, u1} γ α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) g)) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u2} (Set.Elem.{u3} β (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) (Set.Elem.{u2} γ (Function.support.{u2, u1} γ α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) g))) e x))) (f (Subtype.val.{succ u3} β (fun (x : β) => Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) x (Function.support.{u3, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f)) x))) -> (Eq.{succ u1} α (tsum.{u1, u3} α _inst_1 _inst_2 β (fun (x : β) => f x)) (tsum.{u1, u2} α _inst_1 _inst_2 γ (fun (y : γ) => g y)))
Case conversion may be inaccurate. Consider using '#align equiv.tsum_eq_tsum_of_support Equiv.tsum_eq_tsum_of_supportₓ'. -/
theorem Equiv.tsum_eq_tsum_of_support {f : β → α} {g : γ → α} (e : support f ≃ support g)
    (he : ∀ x, g (e x) = f x) : (∑' x, f x) = ∑' y, g y :=
  tsum_eq_tsum_of_hasSum_iff_hasSum fun _ => e.hasSum_iff_of_support he
#align equiv.tsum_eq_tsum_of_support Equiv.tsum_eq_tsum_of_support

/- warning: tsum_eq_tsum_of_ne_zero_bij -> tsum_eq_tsum_of_ne_zero_bij is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} {g : γ -> α} (i : (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) -> β), (forall {{x : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)}} {{y : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)}}, (Eq.{succ u2} β (i x) (i y)) -> (Eq.{succ u3} γ ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)))))) x) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)))))) y))) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f) (Set.range.{u2, succ u3} β (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) i)) -> (forall (x : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)), Eq.{succ u1} α (f (i x)) (g ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x (Function.support.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) g)))))) x))) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (x : β) => f x)) (tsum.{u1, u3} α _inst_1 _inst_2 γ (fun (y : γ) => g y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] {f : β -> α} {g : γ -> α} (i : (Set.Elem.{u3} γ (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)) -> β), (forall {{x : Set.Elem.{u3} γ (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)}} {{y : Set.Elem.{u3} γ (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)}}, (Eq.{succ u1} β (i x) (i y)) -> (Eq.{succ u3} γ (Subtype.val.{succ u3} γ (fun (x : γ) => Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) x (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)) x) (Subtype.val.{succ u3} γ (fun (x : γ) => Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) x (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)) y))) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Function.support.{u1, u2} β α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) f) (Set.range.{u1, succ u3} β (Set.Elem.{u3} γ (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)) i)) -> (forall (x : Set.Elem.{u3} γ (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)), Eq.{succ u2} α (f (i x)) (g (Subtype.val.{succ u3} γ (fun (x : γ) => Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) x (Function.support.{u3, u2} γ α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)) g)) x))) -> (Eq.{succ u2} α (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (x : β) => f x)) (tsum.{u2, u3} α _inst_1 _inst_2 γ (fun (y : γ) => g y)))
Case conversion may be inaccurate. Consider using '#align tsum_eq_tsum_of_ne_zero_bij tsum_eq_tsum_of_ne_zero_bijₓ'. -/
theorem tsum_eq_tsum_of_ne_zero_bij {g : γ → α} (i : support g → β)
    (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y) (hf : support f ⊆ Set.range i)
    (hfg : ∀ x, f (i x) = g x) : (∑' x, f x) = ∑' y, g y :=
  tsum_eq_tsum_of_hasSum_iff_hasSum fun _ => hasSum_iff_hasSum_of_ne_zero_bij i hi hf hfg
#align tsum_eq_tsum_of_ne_zero_bij tsum_eq_tsum_of_ne_zero_bij

/-! ### `tsum` on subsets -/


#print Finset.tsum_subtype /-
@[simp]
theorem Finset.tsum_subtype (s : Finset β) (f : β → α) :
    (∑' x : { x // x ∈ s }, f x) = ∑ x in s, f x :=
  (s.HasSum f).tsum_eq
#align finset.tsum_subtype Finset.tsum_subtype
-/

#print Finset.tsum_subtype' /-
@[simp]
theorem Finset.tsum_subtype' (s : Finset β) (f : β → α) :
    (∑' x : (s : Set β), f x) = ∑ x in s, f x :=
  s.tsum_subtype f
#align finset.tsum_subtype' Finset.tsum_subtype'
-/

/- warning: tsum_subtype -> tsum_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] (s : Set.{u2} β) (f : β -> α), Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) x))) (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (x : β) => Set.indicator.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) s f x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] (s : Set.{u2} β) (f : β -> α), Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 (Set.Elem.{u2} β s) (fun (x : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) x))) (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (x : β) => Set.indicator.{u2, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) s f x))
Case conversion may be inaccurate. Consider using '#align tsum_subtype tsum_subtypeₓ'. -/
theorem tsum_subtype (s : Set β) (f : β → α) : (∑' x : s, f x) = ∑' x, s.indicator f x :=
  tsum_eq_tsum_of_hasSum_iff_hasSum fun _ => hasSum_subtype_iff_indicator
#align tsum_subtype tsum_subtype

/- warning: tsum_subtype_eq_of_support_subset -> tsum_subtype_eq_of_support_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} {s : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Function.support.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) f) s) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) x))) (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (x : β) => f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} {s : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (Function.support.{u2, u1} β α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) f) s) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 (Set.Elem.{u2} β s) (fun (x : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) x))) (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (x : β) => f x)))
Case conversion may be inaccurate. Consider using '#align tsum_subtype_eq_of_support_subset tsum_subtype_eq_of_support_subsetₓ'. -/
theorem tsum_subtype_eq_of_support_subset {f : β → α} {s : Set β} (hs : support f ⊆ s) :
    (∑' x : s, f x) = ∑' x, f x :=
  tsum_eq_tsum_of_hasSum_iff_hasSum fun x => hasSum_subtype_iff_of_support_subset hs
#align tsum_subtype_eq_of_support_subset tsum_subtype_eq_of_support_subset

/- warning: tsum_univ -> tsum_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] (f : β -> α), Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.univ.{u2} β)) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.univ.{u2} β)) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.univ.{u2} β)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.univ.{u2} β)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.univ.{u2} β)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.univ.{u2} β)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.univ.{u2} β)))))) x))) (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (x : β) => f x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] (f : β -> α), Eq.{succ u2} α (tsum.{u2, u1} α _inst_1 _inst_2 (Set.Elem.{u1} β (Set.univ.{u1} β)) (fun (x : Set.Elem.{u1} β (Set.univ.{u1} β)) => f (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.univ.{u1} β)) x))) (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (x : β) => f x))
Case conversion may be inaccurate. Consider using '#align tsum_univ tsum_univₓ'. -/
@[simp]
theorem tsum_univ (f : β → α) : (∑' x : (Set.univ : Set β), f x) = ∑' x, f x :=
  tsum_subtype_eq_of_support_subset <| Set.subset_univ _
#align tsum_univ tsum_univ

/- warning: tsum_singleton -> tsum_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] (b : β) (f : β -> α), Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)))))) x))) (f b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] (b : β) (f : β -> α), Eq.{succ u2} α (tsum.{u2, u1} α _inst_1 _inst_2 (Set.Elem.{u1} β (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) (fun (x : Set.Elem.{u1} β (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) => f (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) x))) (f b)
Case conversion may be inaccurate. Consider using '#align tsum_singleton tsum_singletonₓ'. -/
@[simp]
theorem tsum_singleton (b : β) (f : β → α) : (∑' x : ({b} : Set β), f x) = f b :=
  by
  rw [tsum_subtype, tsum_eq_single b]
  · simp
  · intro b' hb'
    rw [Set.indicator_of_not_mem]
    rwa [Set.mem_singleton_iff]
  · infer_instance
#align tsum_singleton tsum_singleton

#print tsum_image /-
theorem tsum_image {g : γ → β} (f : β → α) {s : Set γ} (hg : Set.InjOn g s) :
    (∑' x : g '' s, f x) = ∑' x : s, f (g x) :=
  ((Equiv.Set.imageOfInjOn _ _ hg).tsum_eq fun x => f x).symm
#align tsum_image tsum_image
-/

#print tsum_range /-
theorem tsum_range {g : γ → β} (f : β → α) (hg : Injective g) :
    (∑' x : Set.range g, f x) = ∑' x, f (g x) := by
  rw [← Set.image_univ, tsum_image f (hg.inj_on _), tsum_univ (f ∘ g)]
#align tsum_range tsum_range
-/

section ContinuousAdd

variable [ContinuousAdd α]

/- warning: tsum_add -> tsum_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} {g : β -> α} [_inst_4 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))], (Summable.{u1, u2} α β _inst_1 _inst_2 f) -> (Summable.{u1, u2} α β _inst_1 _inst_2 g) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (f b) (g b))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => f b)) (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => g b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] {f : β -> α} {g : β -> α} [_inst_4 : ContinuousAdd.{u2} α _inst_2 (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))], (Summable.{u2, u1} α β _inst_1 _inst_2 f) -> (Summable.{u2, u1} α β _inst_1 _inst_2 g) -> (Eq.{succ u2} α (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))) (f b) (g b))) (HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))) (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => f b)) (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => g b))))
Case conversion may be inaccurate. Consider using '#align tsum_add tsum_addₓ'. -/
theorem tsum_add (hf : Summable f) (hg : Summable g) :
    (∑' b, f b + g b) = (∑' b, f b) + ∑' b, g b :=
  (hf.HasSum.add hg.HasSum).tsum_eq
#align tsum_add tsum_add

/- warning: tsum_sum -> tsum_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] [_inst_4 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {f : γ -> β -> α} {s : Finset.{u3} γ}, (forall (i : γ), (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) i s) -> (Summable.{u1, u2} α β _inst_1 _inst_2 (f i))) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => Finset.sum.{u1, u3} α γ _inst_1 s (fun (i : γ) => f i b))) (Finset.sum.{u1, u3} α γ _inst_1 s (fun (i : γ) => tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => f i b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] [_inst_4 : ContinuousAdd.{u2} α _inst_2 (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))] {f : γ -> β -> α} {s : Finset.{u3} γ}, (forall (i : γ), (Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) i s) -> (Summable.{u2, u1} α β _inst_1 _inst_2 (f i))) -> (Eq.{succ u2} α (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => Finset.sum.{u2, u3} α γ _inst_1 s (fun (i : γ) => f i b))) (Finset.sum.{u2, u3} α γ _inst_1 s (fun (i : γ) => tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => f i b))))
Case conversion may be inaccurate. Consider using '#align tsum_sum tsum_sumₓ'. -/
theorem tsum_sum {f : γ → β → α} {s : Finset γ} (hf : ∀ i ∈ s, Summable (f i)) :
    (∑' b, ∑ i in s, f i b) = ∑ i in s, ∑' b, f i b :=
  (hasSum_sum fun i hi => (hf i hi).HasSum).tsum_eq
#align tsum_sum tsum_sum

/- warning: tsum_eq_add_tsum_ite' -> tsum_eq_add_tsum_ite' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] [_inst_4 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {f : β -> α} (b : β), (Summable.{u1, u2} α β _inst_1 _inst_2 (Function.update.{succ u2, succ u1} β (fun (ᾰ : β) => α) (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u2} β a b)) f b (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))))) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (x : β) => f x)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (f b) (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (x : β) => ite.{succ u1} α (Eq.{succ u2} β x b) (Classical.propDecidable (Eq.{succ u2} β x b)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))) (f x)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] [_inst_4 : ContinuousAdd.{u2} α _inst_2 (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))] {f : β -> α} (b : β), (Summable.{u2, u1} α β _inst_1 _inst_2 (Function.update.{succ u1, succ u2} β (fun (ᾰ : β) => α) (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u1} β a b)) f b (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))))) -> (Eq.{succ u2} α (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (x : β) => f x)) (HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))) (f b) (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (x : β) => ite.{succ u2} α (Eq.{succ u1} β x b) (Classical.propDecidable (Eq.{succ u1} β x b)) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)))) (f x)))))
Case conversion may be inaccurate. Consider using '#align tsum_eq_add_tsum_ite' tsum_eq_add_tsum_ite'ₓ'. -/
/-- Version of `tsum_eq_add_tsum_ite` for `add_comm_monoid` rather than `add_comm_group`.
Requires a different convergence assumption involving `function.update`. -/
theorem tsum_eq_add_tsum_ite' {f : β → α} (b : β) (hf : Summable (f.update b 0)) :
    (∑' x, f x) = f b + ∑' x, ite (x = b) 0 (f x) :=
  calc
    (∑' x, f x) = ∑' x, ite (x = b) (f x) 0 + f.update b 0 x :=
      tsum_congr fun n => by split_ifs <;> simp [Function.update_apply, h]
    _ = (∑' x, ite (x = b) (f x) 0) + ∑' x, f.update b 0 x :=
      (tsum_add ⟨ite (b = b) (f b) 0, hasSum_single b fun b hb => if_neg hb⟩ hf)
    _ = ite (b = b) (f b) 0 + ∑' x, f.update b 0 x :=
      by
      congr
      exact tsum_eq_single b fun b' hb' => if_neg hb'
    _ = f b + ∑' x, ite (x = b) 0 (f x) := by
      simp only [Function.update, eq_self_iff_true, if_true, eq_rec_constant, dite_eq_ite]
    
#align tsum_eq_add_tsum_ite' tsum_eq_add_tsum_ite'

variable [AddCommMonoid δ] [TopologicalSpace δ] [T3Space δ] [ContinuousAdd δ]

/- warning: tsum_sigma' -> tsum_sigma' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {δ : Type.{u2}} [_inst_5 : AddCommMonoid.{u2} δ] [_inst_6 : TopologicalSpace.{u2} δ] [_inst_7 : T3Space.{u2} δ _inst_6] [_inst_8 : ContinuousAdd.{u2} δ _inst_6 (AddZeroClass.toHasAdd.{u2} δ (AddMonoid.toAddZeroClass.{u2} δ (AddCommMonoid.toAddMonoid.{u2} δ _inst_5)))] {γ : β -> Type.{u3}} {f : (Sigma.{u1, u3} β (fun (b : β) => γ b)) -> δ}, (forall (b : β), Summable.{u2, u3} δ (γ b) _inst_5 _inst_6 (fun (c : γ b) => f (Sigma.mk.{u1, u3} β (fun (b : β) => γ b) b c))) -> (Summable.{u2, max u1 u3} δ (Sigma.{u1, u3} β (fun (b : β) => γ b)) _inst_5 _inst_6 f) -> (Eq.{succ u2} δ (tsum.{u2, max u1 u3} δ _inst_5 _inst_6 (Sigma.{u1, u3} β (fun (b : β) => γ b)) (fun (p : Sigma.{u1, u3} β (fun (b : β) => γ b)) => f p)) (tsum.{u2, u1} δ _inst_5 _inst_6 β (fun (b : β) => tsum.{u2, u3} δ _inst_5 _inst_6 (γ b) (fun (c : γ b) => f (Sigma.mk.{u1, u3} β (fun (b : β) => γ b) b c)))))
but is expected to have type
  forall {β : Type.{u2}} {δ : Type.{u1}} [_inst_5 : AddCommMonoid.{u1} δ] [_inst_6 : TopologicalSpace.{u1} δ] [_inst_7 : T3Space.{u1} δ _inst_6] [_inst_8 : ContinuousAdd.{u1} δ _inst_6 (AddZeroClass.toAdd.{u1} δ (AddMonoid.toAddZeroClass.{u1} δ (AddCommMonoid.toAddMonoid.{u1} δ _inst_5)))] {γ : β -> Type.{u3}} {f : (Sigma.{u2, u3} β (fun (b : β) => γ b)) -> δ}, (forall (b : β), Summable.{u1, u3} δ (γ b) _inst_5 _inst_6 (fun (c : γ b) => f (Sigma.mk.{u2, u3} β (fun (b : β) => γ b) b c))) -> (Summable.{u1, max u2 u3} δ (Sigma.{u2, u3} β (fun (b : β) => γ b)) _inst_5 _inst_6 f) -> (Eq.{succ u1} δ (tsum.{u1, max u2 u3} δ _inst_5 _inst_6 (Sigma.{u2, u3} β (fun (b : β) => γ b)) (fun (p : Sigma.{u2, u3} β (fun (b : β) => γ b)) => f p)) (tsum.{u1, u2} δ _inst_5 _inst_6 β (fun (b : β) => tsum.{u1, u3} δ _inst_5 _inst_6 (γ b) (fun (c : γ b) => f (Sigma.mk.{u2, u3} β (fun (b : β) => γ b) b c)))))
Case conversion may be inaccurate. Consider using '#align tsum_sigma' tsum_sigma'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
theorem tsum_sigma' {γ : β → Type _} {f : (Σb : β, γ b) → δ} (h₁ : ∀ b, Summable fun c => f ⟨b, c⟩)
    (h₂ : Summable f) : (∑' p, f p) = ∑' (b) (c), f ⟨b, c⟩ :=
  (h₂.HasSum.Sigma fun b => (h₁ b).HasSum).tsum_eq.symm
#align tsum_sigma' tsum_sigma'

/- warning: tsum_prod' -> tsum_prod' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} {δ : Type.{u3}} [_inst_5 : AddCommMonoid.{u3} δ] [_inst_6 : TopologicalSpace.{u3} δ] [_inst_7 : T3Space.{u3} δ _inst_6] [_inst_8 : ContinuousAdd.{u3} δ _inst_6 (AddZeroClass.toHasAdd.{u3} δ (AddMonoid.toAddZeroClass.{u3} δ (AddCommMonoid.toAddMonoid.{u3} δ _inst_5)))] {f : (Prod.{u1, u2} β γ) -> δ}, (Summable.{u3, max u1 u2} δ (Prod.{u1, u2} β γ) _inst_5 _inst_6 f) -> (forall (b : β), Summable.{u3, u2} δ γ _inst_5 _inst_6 (fun (c : γ) => f (Prod.mk.{u1, u2} β γ b c))) -> (Eq.{succ u3} δ (tsum.{u3, max u1 u2} δ _inst_5 _inst_6 (Prod.{u1, u2} β γ) (fun (p : Prod.{u1, u2} β γ) => f p)) (tsum.{u3, u1} δ _inst_5 _inst_6 β (fun (b : β) => tsum.{u3, u2} δ _inst_5 _inst_6 γ (fun (c : γ) => f (Prod.mk.{u1, u2} β γ b c)))))
but is expected to have type
  forall {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_5 : AddCommMonoid.{u1} δ] [_inst_6 : TopologicalSpace.{u1} δ] [_inst_7 : T3Space.{u1} δ _inst_6] [_inst_8 : ContinuousAdd.{u1} δ _inst_6 (AddZeroClass.toAdd.{u1} δ (AddMonoid.toAddZeroClass.{u1} δ (AddCommMonoid.toAddMonoid.{u1} δ _inst_5)))] {f : (Prod.{u3, u2} β γ) -> δ}, (Summable.{u1, max u3 u2} δ (Prod.{u3, u2} β γ) _inst_5 _inst_6 f) -> (forall (b : β), Summable.{u1, u2} δ γ _inst_5 _inst_6 (fun (c : γ) => f (Prod.mk.{u3, u2} β γ b c))) -> (Eq.{succ u1} δ (tsum.{u1, max u3 u2} δ _inst_5 _inst_6 (Prod.{u3, u2} β γ) (fun (p : Prod.{u3, u2} β γ) => f p)) (tsum.{u1, u3} δ _inst_5 _inst_6 β (fun (b : β) => tsum.{u1, u2} δ _inst_5 _inst_6 γ (fun (c : γ) => f (Prod.mk.{u3, u2} β γ b c)))))
Case conversion may be inaccurate. Consider using '#align tsum_prod' tsum_prod'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
theorem tsum_prod' {f : β × γ → δ} (h : Summable f) (h₁ : ∀ b, Summable fun c => f (b, c)) :
    (∑' p, f p) = ∑' (b) (c), f (b, c) :=
  (h.HasSum.prod_fiberwise fun b => (h₁ b).HasSum).tsum_eq.symm
#align tsum_prod' tsum_prod'

/- warning: tsum_comm' -> tsum_comm' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} {δ : Type.{u3}} [_inst_5 : AddCommMonoid.{u3} δ] [_inst_6 : TopologicalSpace.{u3} δ] [_inst_7 : T3Space.{u3} δ _inst_6] [_inst_8 : ContinuousAdd.{u3} δ _inst_6 (AddZeroClass.toHasAdd.{u3} δ (AddMonoid.toAddZeroClass.{u3} δ (AddCommMonoid.toAddMonoid.{u3} δ _inst_5)))] {f : β -> γ -> δ}, (Summable.{u3, max u1 u2} δ (Prod.{u1, u2} β γ) _inst_5 _inst_6 (Function.uncurry.{u1, u2, u3} β γ δ f)) -> (forall (b : β), Summable.{u3, u2} δ γ _inst_5 _inst_6 (f b)) -> (forall (c : γ), Summable.{u3, u1} δ β _inst_5 _inst_6 (fun (b : β) => f b c)) -> (Eq.{succ u3} δ (tsum.{u3, u2} δ _inst_5 _inst_6 γ (fun (c : γ) => tsum.{u3, u1} δ _inst_5 _inst_6 β (fun (b : β) => f b c))) (tsum.{u3, u1} δ _inst_5 _inst_6 β (fun (b : β) => tsum.{u3, u2} δ _inst_5 _inst_6 γ (fun (c : γ) => f b c))))
but is expected to have type
  forall {β : Type.{u1}} {γ : Type.{u2}} {δ : Type.{u3}} [_inst_5 : AddCommMonoid.{u3} δ] [_inst_6 : TopologicalSpace.{u3} δ] [_inst_7 : T3Space.{u3} δ _inst_6] [_inst_8 : ContinuousAdd.{u3} δ _inst_6 (AddZeroClass.toAdd.{u3} δ (AddMonoid.toAddZeroClass.{u3} δ (AddCommMonoid.toAddMonoid.{u3} δ _inst_5)))] {f : β -> γ -> δ}, (Summable.{u3, max u2 u1} δ (Prod.{u1, u2} β γ) _inst_5 _inst_6 (Function.uncurry.{u1, u2, u3} β γ δ f)) -> (forall (b : β), Summable.{u3, u2} δ γ _inst_5 _inst_6 (f b)) -> (forall (c : γ), Summable.{u3, u1} δ β _inst_5 _inst_6 (fun (b : β) => f b c)) -> (Eq.{succ u3} δ (tsum.{u3, u2} δ _inst_5 _inst_6 γ (fun (c : γ) => tsum.{u3, u1} δ _inst_5 _inst_6 β (fun (b : β) => f b c))) (tsum.{u3, u1} δ _inst_5 _inst_6 β (fun (b : β) => tsum.{u3, u2} δ _inst_5 _inst_6 γ (fun (c : γ) => f b c))))
Case conversion may be inaccurate. Consider using '#align tsum_comm' tsum_comm'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (c b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
theorem tsum_comm' {f : β → γ → δ} (h : Summable (Function.uncurry f)) (h₁ : ∀ b, Summable (f b))
    (h₂ : ∀ c, Summable fun b => f b c) : (∑' (c) (b), f b c) = ∑' (b) (c), f b c :=
  by
  erw [← tsum_prod' h h₁, ← tsum_prod' h.prod_symm h₂, ← (Equiv.prodComm γ β).tsum_eq (uncurry f)]
  rfl
#align tsum_comm' tsum_comm'

end ContinuousAdd

open Encodable

section Encodable

variable [Encodable γ]

/- warning: tsum_supr_decode₂ -> tsum_supᵢ_decode₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] [_inst_4 : Encodable.{u3} γ] [_inst_5 : CompleteLattice.{u2} β] (m : β -> α), (Eq.{succ u1} α (m (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β _inst_5))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))))) -> (forall (s : γ -> β), Eq.{succ u1} α (tsum.{u1, 0} α _inst_1 _inst_2 Nat (fun (i : Nat) => m (supᵢ.{u2, succ u3} β (ConditionallyCompleteLattice.toHasSup.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_5)) γ (fun (b : γ) => supᵢ.{u2, 0} β (ConditionallyCompleteLattice.toHasSup.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_5)) (Membership.Mem.{u3, u3} γ (Option.{u3} γ) (Option.hasMem.{u3} γ) b (Encodable.decode₂.{u3} γ _inst_4 i)) (fun (H : Membership.Mem.{u3, u3} γ (Option.{u3} γ) (Option.hasMem.{u3} γ) b (Encodable.decode₂.{u3} γ _inst_4 i)) => s b))))) (tsum.{u1, u3} α _inst_1 _inst_2 γ (fun (b : γ) => m (s b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] [_inst_4 : Encodable.{u1} γ] [_inst_5 : CompleteLattice.{u3} β] (m : β -> α), (Eq.{succ u2} α (m (Bot.bot.{u3} β (CompleteLattice.toBot.{u3} β _inst_5))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))))) -> (forall (s : γ -> β), Eq.{succ u2} α (tsum.{u2, 0} α _inst_1 _inst_2 Nat (fun (i : Nat) => m (supᵢ.{u3, succ u1} β (ConditionallyCompleteLattice.toSupSet.{u3} β (CompleteLattice.toConditionallyCompleteLattice.{u3} β _inst_5)) γ (fun (b : γ) => supᵢ.{u3, 0} β (ConditionallyCompleteLattice.toSupSet.{u3} β (CompleteLattice.toConditionallyCompleteLattice.{u3} β _inst_5)) (Membership.mem.{u1, u1} γ (Option.{u1} γ) (Option.instMembershipOption.{u1} γ) b (Encodable.decode₂.{u1} γ _inst_4 i)) (fun (H : Membership.mem.{u1, u1} γ (Option.{u1} γ) (Option.instMembershipOption.{u1} γ) b (Encodable.decode₂.{u1} γ _inst_4 i)) => s b))))) (tsum.{u2, u1} α _inst_1 _inst_2 γ (fun (b : γ) => m (s b))))
Case conversion may be inaccurate. Consider using '#align tsum_supr_decode₂ tsum_supᵢ_decode₂ₓ'. -/
/-- You can compute a sum over an encodably type by summing over the natural numbers and
  taking a supremum. This is useful for outer measures. -/
theorem tsum_supᵢ_decode₂ [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (s : γ → β) :
    (∑' i : ℕ, m (⨆ b ∈ decode₂ γ i, s b)) = ∑' b : γ, m (s b) :=
  by
  have H : ∀ n, m (⨆ b ∈ decode₂ γ n, s b) ≠ 0 → (decode₂ γ n).isSome :=
    by
    intro n h
    cases' decode₂ γ n with b
    · refine' (h <| by simp [m0]).elim
    · exact rfl
  symm
  refine' tsum_eq_tsum_of_ne_zero_bij (fun a => Option.get (H a.1 a.2)) _ _ _
  · rintro ⟨m, hm⟩ ⟨n, hn⟩ e
    have := mem_decode₂.1 (Option.get_mem (H n hn))
    rwa [← e, mem_decode₂.1 (Option.get_mem (H m hm))] at this
  · intro b h
    refine' ⟨⟨encode b, _⟩, _⟩
    · simp only [mem_support, encodek₂] at h⊢
      convert h
      simp [Set.ext_iff, encodek₂]
    · exact Option.get_of_mem _ (encodek₂ _)
  · rintro ⟨n, h⟩
    dsimp only [Subtype.coe_mk]
    trans
    swap
    rw [show decode₂ γ n = _ from Option.get_mem (H n h)]
    congr
    simp [ext_iff, -Option.some_get]
#align tsum_supr_decode₂ tsum_supᵢ_decode₂

/- warning: tsum_Union_decode₂ -> tsum_unionᵢ_decode₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] [_inst_4 : Encodable.{u3} γ] (m : (Set.{u2} β) -> α), (Eq.{succ u1} α (m (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))))) -> (forall (s : γ -> (Set.{u2} β)), Eq.{succ u1} α (tsum.{u1, 0} α _inst_1 _inst_2 Nat (fun (i : Nat) => m (Set.unionᵢ.{u2, succ u3} β γ (fun (b : γ) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} γ (Option.{u3} γ) (Option.hasMem.{u3} γ) b (Encodable.decode₂.{u3} γ _inst_4 i)) (fun (H : Membership.Mem.{u3, u3} γ (Option.{u3} γ) (Option.hasMem.{u3} γ) b (Encodable.decode₂.{u3} γ _inst_4 i)) => s b))))) (tsum.{u1, u3} α _inst_1 _inst_2 γ (fun (b : γ) => m (s b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] [_inst_4 : Encodable.{u1} γ] (m : (Set.{u3} β) -> α), (Eq.{succ u2} α (m (EmptyCollection.emptyCollection.{u3} (Set.{u3} β) (Set.instEmptyCollectionSet.{u3} β))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))))) -> (forall (s : γ -> (Set.{u3} β)), Eq.{succ u2} α (tsum.{u2, 0} α _inst_1 _inst_2 Nat (fun (i : Nat) => m (Set.unionᵢ.{u3, succ u1} β γ (fun (b : γ) => Set.unionᵢ.{u3, 0} β (Membership.mem.{u1, u1} γ (Option.{u1} γ) (Option.instMembershipOption.{u1} γ) b (Encodable.decode₂.{u1} γ _inst_4 i)) (fun (H : Membership.mem.{u1, u1} γ (Option.{u1} γ) (Option.instMembershipOption.{u1} γ) b (Encodable.decode₂.{u1} γ _inst_4 i)) => s b))))) (tsum.{u2, u1} α _inst_1 _inst_2 γ (fun (b : γ) => m (s b))))
Case conversion may be inaccurate. Consider using '#align tsum_Union_decode₂ tsum_unionᵢ_decode₂ₓ'. -/
/-- `tsum_supr_decode₂` specialized to the complete lattice of sets. -/
theorem tsum_unionᵢ_decode₂ (m : Set β → α) (m0 : m ∅ = 0) (s : γ → Set β) :
    (∑' i, m (⋃ b ∈ decode₂ γ i, s b)) = ∑' b, m (s b) :=
  tsum_supᵢ_decode₂ m m0 s
#align tsum_Union_decode₂ tsum_unionᵢ_decode₂

end Encodable

/-! Some properties about measure-like functions.
  These could also be functions defined on complete sublattices of sets, with the property
  that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/


section Countable

variable [Countable γ]

/- warning: rel_supr_tsum -> rel_supᵢ_tsum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] [_inst_4 : Countable.{succ u3} γ] [_inst_5 : CompleteLattice.{u2} β] (m : β -> α), (Eq.{succ u1} α (m (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β _inst_5))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))))) -> (forall (R : α -> α -> Prop), (forall (s : Nat -> β), R (m (supᵢ.{u2, 1} β (ConditionallyCompleteLattice.toHasSup.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_5)) Nat (fun (i : Nat) => s i))) (tsum.{u1, 0} α _inst_1 _inst_2 Nat (fun (i : Nat) => m (s i)))) -> (forall (s : γ -> β), R (m (supᵢ.{u2, succ u3} β (ConditionallyCompleteLattice.toHasSup.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_5)) γ (fun (b : γ) => s b))) (tsum.{u1, u3} α _inst_1 _inst_2 γ (fun (b : γ) => m (s b)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] [_inst_4 : Countable.{succ u1} γ] [_inst_5 : CompleteLattice.{u3} β] (m : β -> α), (Eq.{succ u2} α (m (Bot.bot.{u3} β (CompleteLattice.toBot.{u3} β _inst_5))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))))) -> (forall (R : α -> α -> Prop), (forall (s : Nat -> β), R (m (supᵢ.{u3, 1} β (ConditionallyCompleteLattice.toSupSet.{u3} β (CompleteLattice.toConditionallyCompleteLattice.{u3} β _inst_5)) Nat (fun (i : Nat) => s i))) (tsum.{u2, 0} α _inst_1 _inst_2 Nat (fun (i : Nat) => m (s i)))) -> (forall (s : γ -> β), R (m (supᵢ.{u3, succ u1} β (ConditionallyCompleteLattice.toSupSet.{u3} β (CompleteLattice.toConditionallyCompleteLattice.{u3} β _inst_5)) γ (fun (b : γ) => s b))) (tsum.{u2, u1} α _inst_1 _inst_2 γ (fun (b : γ) => m (s b)))))
Case conversion may be inaccurate. Consider using '#align rel_supr_tsum rel_supᵢ_tsumₓ'. -/
/-- If a function is countably sub-additive then it is sub-additive on countable types -/
theorem rel_supᵢ_tsum [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
    (m_supr : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∑' i, m (s i))) (s : γ → β) :
    R (m (⨆ b : γ, s b)) (∑' b : γ, m (s b)) :=
  by
  cases nonempty_encodable γ
  rw [← supr_decode₂, ← tsum_supᵢ_decode₂ _ m0 s]
  exact m_supr _
#align rel_supr_tsum rel_supᵢ_tsum

/- warning: rel_supr_sum -> rel_supᵢ_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {δ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] [_inst_5 : CompleteLattice.{u2} β] (m : β -> α), (Eq.{succ u1} α (m (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β _inst_5))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))))) -> (forall (R : α -> α -> Prop), (forall (s : Nat -> β), R (m (supᵢ.{u2, 1} β (ConditionallyCompleteLattice.toHasSup.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_5)) Nat (fun (i : Nat) => s i))) (tsum.{u1, 0} α _inst_1 _inst_2 Nat (fun (i : Nat) => m (s i)))) -> (forall (s : δ -> β) (t : Finset.{u3} δ), R (m (supᵢ.{u2, succ u3} β (ConditionallyCompleteLattice.toHasSup.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_5)) δ (fun (d : δ) => supᵢ.{u2, 0} β (ConditionallyCompleteLattice.toHasSup.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_5)) (Membership.Mem.{u3, u3} δ (Finset.{u3} δ) (Finset.hasMem.{u3} δ) d t) (fun (H : Membership.Mem.{u3, u3} δ (Finset.{u3} δ) (Finset.hasMem.{u3} δ) d t) => s d)))) (Finset.sum.{u1, u3} α δ _inst_1 t (fun (d : δ) => m (s d)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {δ : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] [_inst_5 : CompleteLattice.{u3} β] (m : β -> α), (Eq.{succ u2} α (m (Bot.bot.{u3} β (CompleteLattice.toBot.{u3} β _inst_5))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))))) -> (forall (R : α -> α -> Prop), (forall (s : Nat -> β), R (m (supᵢ.{u3, 1} β (ConditionallyCompleteLattice.toSupSet.{u3} β (CompleteLattice.toConditionallyCompleteLattice.{u3} β _inst_5)) Nat (fun (i : Nat) => s i))) (tsum.{u2, 0} α _inst_1 _inst_2 Nat (fun (i : Nat) => m (s i)))) -> (forall (s : δ -> β) (t : Finset.{u1} δ), R (m (supᵢ.{u3, succ u1} β (ConditionallyCompleteLattice.toSupSet.{u3} β (CompleteLattice.toConditionallyCompleteLattice.{u3} β _inst_5)) δ (fun (d : δ) => supᵢ.{u3, 0} β (ConditionallyCompleteLattice.toSupSet.{u3} β (CompleteLattice.toConditionallyCompleteLattice.{u3} β _inst_5)) (Membership.mem.{u1, u1} δ (Finset.{u1} δ) (Finset.instMembershipFinset.{u1} δ) d t) (fun (H : Membership.mem.{u1, u1} δ (Finset.{u1} δ) (Finset.instMembershipFinset.{u1} δ) d t) => s d)))) (Finset.sum.{u2, u1} α δ _inst_1 t (fun (d : δ) => m (s d)))))
Case conversion may be inaccurate. Consider using '#align rel_supr_sum rel_supᵢ_sumₓ'. -/
/-- If a function is countably sub-additive then it is sub-additive on finite sets -/
theorem rel_supᵢ_sum [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
    (m_supr : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∑' i, m (s i))) (s : δ → β) (t : Finset δ) :
    R (m (⨆ d ∈ t, s d)) (∑ d in t, m (s d)) :=
  by
  rw [supᵢ_subtype', ← Finset.tsum_subtype]
  exact rel_supᵢ_tsum m m0 R m_supr _
#align rel_supr_sum rel_supᵢ_sum

/- warning: rel_sup_add -> rel_sup_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] [_inst_5 : CompleteLattice.{u2} β] (m : β -> α), (Eq.{succ u1} α (m (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β _inst_5))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))))) -> (forall (R : α -> α -> Prop), (forall (s : Nat -> β), R (m (supᵢ.{u2, 1} β (ConditionallyCompleteLattice.toHasSup.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_5)) Nat (fun (i : Nat) => s i))) (tsum.{u1, 0} α _inst_1 _inst_2 Nat (fun (i : Nat) => m (s i)))) -> (forall (s₁ : β) (s₂ : β), R (m (Sup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_5)))) s₁ s₂)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (m s₁) (m s₂))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] [_inst_5 : CompleteLattice.{u2} β] (m : β -> α), (Eq.{succ u1} α (m (Bot.bot.{u2} β (CompleteLattice.toBot.{u2} β _inst_5))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))) -> (forall (R : α -> α -> Prop), (forall (s : Nat -> β), R (m (supᵢ.{u2, 1} β (ConditionallyCompleteLattice.toSupSet.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_5)) Nat (fun (i : Nat) => s i))) (tsum.{u1, 0} α _inst_1 _inst_2 Nat (fun (i : Nat) => m (s i)))) -> (forall (s₁ : β) (s₂ : β), R (m (Sup.sup.{u2} β (SemilatticeSup.toSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_5)))) s₁ s₂)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (m s₁) (m s₂))))
Case conversion may be inaccurate. Consider using '#align rel_sup_add rel_sup_addₓ'. -/
/-- If a function is countably sub-additive then it is binary sub-additive -/
theorem rel_sup_add [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
    (m_supr : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∑' i, m (s i))) (s₁ s₂ : β) :
    R (m (s₁ ⊔ s₂)) (m s₁ + m s₂) :=
  by
  convert rel_supᵢ_tsum m m0 R m_supr fun b => cond b s₁ s₂
  · simp only [supᵢ_bool_eq, cond]
  · rw [tsum_fintype, Fintype.sum_bool, cond, cond]
#align rel_sup_add rel_sup_add

end Countable

variable [ContinuousAdd α]

/- warning: tsum_add_tsum_compl -> tsum_add_tsum_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} [_inst_4 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β}, (Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s)))))))) -> (Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s))))))))) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (tsum.{u1, u2} α _inst_1 _inst_2 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) x))) (tsum.{u1, u2} α _inst_1 _inst_2 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)))))) x)))) (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (x : β) => f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} [_inst_4 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β}, (Summable.{u1, u2} α (Set.Elem.{u2} β s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β s) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s)))) -> (Summable.{u1, u2} α (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s))))) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (tsum.{u1, u2} α _inst_1 _inst_2 (Set.Elem.{u2} β s) (fun (x : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) x))) (tsum.{u1, u2} α _inst_1 _inst_2 (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) (fun (x : Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) x)))) (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (x : β) => f x)))
Case conversion may be inaccurate. Consider using '#align tsum_add_tsum_compl tsum_add_tsum_complₓ'. -/
theorem tsum_add_tsum_compl {s : Set β} (hs : Summable (f ∘ coe : s → α))
    (hsc : Summable (f ∘ coe : sᶜ → α)) : ((∑' x : s, f x) + ∑' x : sᶜ, f x) = ∑' x, f x :=
  (hs.HasSum.add_compl hsc.HasSum).tsum_eq.symm
#align tsum_add_tsum_compl tsum_add_tsum_compl

/- warning: tsum_union_disjoint -> tsum_union_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} [_inst_4 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β} {t : Set.{u2} β}, (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) s t) -> (Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s)))))))) -> (Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t)))))))) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)))))) x))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (tsum.{u1, u2} α _inst_1 _inst_2 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) x))) (tsum.{u1, u2} α _inst_1 _inst_2 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t))))) x)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} [_inst_4 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {s : Set.{u2} β} {t : Set.{u2} β}, (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} β) (Preorder.toLE.{u2} (Set.{u2} β) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))) s t) -> (Summable.{u1, u2} α (Set.Elem.{u2} β s) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β s) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s)))) -> (Summable.{u1, u2} α (Set.Elem.{u2} β t) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β t) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t)))) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 (Set.Elem.{u2} β (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) (fun (x : Set.Elem.{u2} β (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) x))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (tsum.{u1, u2} α _inst_1 _inst_2 (Set.Elem.{u2} β s) (fun (x : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) x))) (tsum.{u1, u2} α _inst_1 _inst_2 (Set.Elem.{u2} β t) (fun (x : Set.Elem.{u2} β t) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) x)))))
Case conversion may be inaccurate. Consider using '#align tsum_union_disjoint tsum_union_disjointₓ'. -/
theorem tsum_union_disjoint {s t : Set β} (hd : Disjoint s t) (hs : Summable (f ∘ coe : s → α))
    (ht : Summable (f ∘ coe : t → α)) : (∑' x : s ∪ t, f x) = (∑' x : s, f x) + ∑' x : t, f x :=
  (hs.HasSum.add_disjoint hd ht.HasSum).tsum_eq
#align tsum_union_disjoint tsum_union_disjoint

/- warning: tsum_finset_bUnion_disjoint -> tsum_finset_bUnion_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} [_inst_4 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {ι : Type.{u3}} {s : Finset.{u3} ι} {t : ι -> (Set.{u2} β)}, (Set.Pairwise.{u3} ι ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Finset.{u3} ι) (Set.{u3} ι) (HasLiftT.mk.{succ u3, succ u3} (Finset.{u3} ι) (Set.{u3} ι) (CoeTCₓ.coe.{succ u3, succ u3} (Finset.{u3} ι) (Set.{u3} ι) (Finset.Set.hasCoeT.{u3} ι))) s) (Function.onFun.{succ u3, succ u2, 1} ι (Set.{u2} β) Prop (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))) t)) -> (forall (i : ι), (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) -> (Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (t i)))))))))) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) => t i)))) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) => t i)))) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) => t i)))) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) => t i)))) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) => t i)))) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) => t i)))) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) => t i)))))))) x))) (Finset.sum.{u1, u3} α ι _inst_1 s (fun (i : ι) => tsum.{u1, u2} α _inst_1 _inst_2 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (t i)))))) x)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> α} [_inst_4 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {ι : Type.{u3}} {s : Finset.{u3} ι} {t : ι -> (Set.{u2} β)}, (Set.Pairwise.{u3} ι (Finset.toSet.{u3} ι s) (Function.onFun.{succ u3, succ u2, 1} ι (Set.{u2} β) Prop (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} β) (Preorder.toLE.{u2} (Set.{u2} β) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))))) t)) -> (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) -> (Summable.{u1, u2} α (Set.Elem.{u2} β (t i)) _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β (t i)) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (t i)))))) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 (Set.Elem.{u2} β (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) (fun (H : Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) => t i)))) (fun (x : Set.Elem.{u2} β (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) (fun (H : Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) => t i)))) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Set.unionᵢ.{u2, succ u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, 0} β (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) (fun (h._@.Mathlib.Topology.Algebra.InfiniteSum.Basic._hyg.11412 : Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) => t i)))) x))) (Finset.sum.{u1, u3} α ι _inst_1 s (fun (i : ι) => tsum.{u1, u2} α _inst_1 _inst_2 (Set.Elem.{u2} β (t i)) (fun (x : Set.Elem.{u2} β (t i)) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (t i)) x)))))
Case conversion may be inaccurate. Consider using '#align tsum_finset_bUnion_disjoint tsum_finset_bUnion_disjointₓ'. -/
theorem tsum_finset_bUnion_disjoint {ι} {s : Finset ι} {t : ι → Set β}
    (hd : (s : Set ι).Pairwise (Disjoint on t)) (hf : ∀ i ∈ s, Summable (f ∘ coe : t i → α)) :
    (∑' x : ⋃ i ∈ s, t i, f x) = ∑ i in s, ∑' x : t i, f x :=
  (hasSum_sum_disjoint _ hd fun i hi => (hf i hi).HasSum).tsum_eq
#align tsum_finset_bUnion_disjoint tsum_finset_bUnion_disjoint

/- warning: tsum_even_add_odd -> tsum_even_add_odd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] [_inst_4 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {f : Nat -> α}, (Summable.{u1, 0} α Nat _inst_1 _inst_2 (fun (k : Nat) => f (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k))) -> (Summable.{u1, 0} α Nat _inst_1 _inst_2 (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (tsum.{u1, 0} α _inst_1 _inst_2 Nat (fun (k : Nat) => f (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k))) (tsum.{u1, 0} α _inst_1 _inst_2 Nat (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (tsum.{u1, 0} α _inst_1 _inst_2 Nat (fun (k : Nat) => f k)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] [_inst_4 : ContinuousAdd.{u1} α _inst_2 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))] {f : Nat -> α}, (Summable.{u1, 0} α Nat _inst_1 _inst_2 (fun (k : Nat) => f (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k))) -> (Summable.{u1, 0} α Nat _inst_1 _inst_2 (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (tsum.{u1, 0} α _inst_1 _inst_2 Nat (fun (k : Nat) => f (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k))) (tsum.{u1, 0} α _inst_1 _inst_2 Nat (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (tsum.{u1, 0} α _inst_1 _inst_2 Nat (fun (k : Nat) => f k)))
Case conversion may be inaccurate. Consider using '#align tsum_even_add_odd tsum_even_add_oddₓ'. -/
theorem tsum_even_add_odd {f : ℕ → α} (he : Summable fun k => f (2 * k))
    (ho : Summable fun k => f (2 * k + 1)) :
    ((∑' k, f (2 * k)) + ∑' k, f (2 * k + 1)) = ∑' k, f k :=
  (he.HasSum.even_add_odd ho.HasSum).tsum_eq.symm
#align tsum_even_add_odd tsum_even_add_odd

end tsum

section TopologicalGroup

variable [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α]

variable {f g : β → α} {a a₁ a₂ : α}

/- warning: has_sum.neg -> HasSum.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {a : α}, (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f a) -> (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (b : β) => Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) (f b)) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α} {a : α}, (HasSum.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a) -> (HasSum.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (b : β) => Neg.neg.{u2} α (NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α _inst_1))))) (f b)) (Neg.neg.{u2} α (NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α _inst_1))))) a))
Case conversion may be inaccurate. Consider using '#align has_sum.neg HasSum.negₓ'. -/
-- `by simpa using` speeds up elaboration. Why?
theorem HasSum.neg (h : HasSum f a) : HasSum (fun b => -f b) (-a) := by
  simpa only using h.map (-AddMonoidHom.id α) continuous_neg
#align has_sum.neg HasSum.neg

/- warning: summable.neg -> Summable.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α}, (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f) -> (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (b : β) => Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) (f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α}, (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (b : β) => Neg.neg.{u2} α (NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α _inst_1))))) (f b)))
Case conversion may be inaccurate. Consider using '#align summable.neg Summable.negₓ'. -/
theorem Summable.neg (hf : Summable f) : Summable fun b => -f b :=
  hf.HasSum.neg.Summable
#align summable.neg Summable.neg

/- warning: summable.of_neg -> Summable.of_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α}, (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (b : β) => Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) (f b))) -> (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α}, (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (b : β) => Neg.neg.{u2} α (NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α _inst_1))))) (f b))) -> (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 f)
Case conversion may be inaccurate. Consider using '#align summable.of_neg Summable.of_negₓ'. -/
theorem Summable.of_neg (hf : Summable fun b => -f b) : Summable f := by
  simpa only [neg_neg] using hf.neg
#align summable.of_neg Summable.of_neg

/- warning: summable_neg_iff -> summable_neg_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α}, Iff (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (b : β) => Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) (f b))) (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α}, Iff (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (b : β) => Neg.neg.{u2} α (NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α _inst_1))))) (f b))) (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 f)
Case conversion may be inaccurate. Consider using '#align summable_neg_iff summable_neg_iffₓ'. -/
theorem summable_neg_iff : (Summable fun b => -f b) ↔ Summable f :=
  ⟨Summable.of_neg, Summable.neg⟩
#align summable_neg_iff summable_neg_iff

/- warning: has_sum.sub -> HasSum.sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {g : β -> α} {a₁ : α} {a₂ : α}, (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f a₁) -> (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 g a₂) -> (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (b : β) => HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) (f b) (g b)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a₁ a₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α} {g : β -> α} {a₁ : α} {a₂ : α}, (HasSum.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a₁) -> (HasSum.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 g a₂) -> (HasSum.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (b : β) => HSub.hSub.{u2, u2, u2} α α α (instHSub.{u2} α (SubNegMonoid.toSub.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α _inst_1)))) (f b) (g b)) (HSub.hSub.{u2, u2, u2} α α α (instHSub.{u2} α (SubNegMonoid.toSub.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α _inst_1)))) a₁ a₂))
Case conversion may be inaccurate. Consider using '#align has_sum.sub HasSum.subₓ'. -/
theorem HasSum.sub (hf : HasSum f a₁) (hg : HasSum g a₂) : HasSum (fun b => f b - g b) (a₁ - a₂) :=
  by
  simp only [sub_eq_add_neg]
  exact hf.add hg.neg
#align has_sum.sub HasSum.sub

/- warning: summable.sub -> Summable.sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {g : β -> α}, (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f) -> (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 g) -> (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (b : β) => HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) (f b) (g b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α} {g : β -> α}, (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 g) -> (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (b : β) => HSub.hSub.{u2, u2, u2} α α α (instHSub.{u2} α (SubNegMonoid.toSub.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α _inst_1)))) (f b) (g b)))
Case conversion may be inaccurate. Consider using '#align summable.sub Summable.subₓ'. -/
theorem Summable.sub (hf : Summable f) (hg : Summable g) : Summable fun b => f b - g b :=
  (hf.HasSum.sub hg.HasSum).Summable
#align summable.sub Summable.sub

/- warning: summable.trans_sub -> Summable.trans_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {g : β -> α}, (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 g) -> (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (b : β) => HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) (f b) (g b))) -> (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α} {g : β -> α}, (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 g) -> (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (b : β) => HSub.hSub.{u2, u2, u2} α α α (instHSub.{u2} α (SubNegMonoid.toSub.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α _inst_1)))) (f b) (g b))) -> (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 f)
Case conversion may be inaccurate. Consider using '#align summable.trans_sub Summable.trans_subₓ'. -/
theorem Summable.trans_sub (hg : Summable g) (hfg : Summable fun b => f b - g b) : Summable f := by
  simpa only [sub_add_cancel] using hfg.add hg
#align summable.trans_sub Summable.trans_sub

/- warning: summable_iff_of_summable_sub -> summable_iff_of_summable_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {g : β -> α}, (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (b : β) => HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) (f b) (g b))) -> (Iff (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f) (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α} {g : β -> α}, (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (b : β) => HSub.hSub.{u2, u2, u2} α α α (instHSub.{u2} α (SubNegMonoid.toSub.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α _inst_1)))) (f b) (g b))) -> (Iff (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 g))
Case conversion may be inaccurate. Consider using '#align summable_iff_of_summable_sub summable_iff_of_summable_subₓ'. -/
theorem summable_iff_of_summable_sub (hfg : Summable fun b => f b - g b) :
    Summable f ↔ Summable g :=
  ⟨fun hf => hf.trans_sub <| by simpa only [neg_sub] using hfg.neg, fun hg => hg.trans_sub hfg⟩
#align summable_iff_of_summable_sub summable_iff_of_summable_sub

/- warning: has_sum.update -> HasSum.update is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {a₁ : α}, (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f a₁) -> (forall (b : β) [_inst_4 : DecidableEq.{succ u2} β] (a : α), HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.update.{succ u2, succ u1} β (fun (ᾰ : β) => α) (fun (a : β) (b : β) => _inst_4 a b) f b a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a (f b)) a₁))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α} {a₁ : α}, (HasSum.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a₁) -> (forall (b : β) [_inst_4 : DecidableEq.{succ u1} β] (a : α), HasSum.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 (Function.update.{succ u1, succ u2} β (fun (ᾰ : β) => α) (fun (a : β) (b : β) => _inst_4 a b) f b a) (HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (SubNegMonoid.toAddMonoid.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α _inst_1)))))) (HSub.hSub.{u2, u2, u2} α α α (instHSub.{u2} α (SubNegMonoid.toSub.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α _inst_1)))) a (f b)) a₁))
Case conversion may be inaccurate. Consider using '#align has_sum.update HasSum.updateₓ'. -/
theorem HasSum.update (hf : HasSum f a₁) (b : β) [DecidableEq β] (a : α) :
    HasSum (update f b a) (a - f b + a₁) :=
  by
  convert (hasSum_ite_eq b _).add hf
  ext b'
  by_cases h : b' = b
  · rw [h, update_same]
    simp only [eq_self_iff_true, if_true, sub_add_cancel]
  simp only [h, update_noteq, if_false, Ne.def, zero_add, not_false_iff]
#align has_sum.update HasSum.update

/- warning: summable.update -> Summable.update is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α}, (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f) -> (forall (b : β) [_inst_4 : DecidableEq.{succ u2} β] (a : α), Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.update.{succ u2, succ u1} β (fun (ᾰ : β) => α) (fun (a : β) (b : β) => _inst_4 a b) f b a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α}, (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (forall (b : β) [_inst_4 : DecidableEq.{succ u1} β] (a : α), Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 (Function.update.{succ u1, succ u2} β (fun (ᾰ : β) => α) (fun (a : β) (b : β) => _inst_4 a b) f b a))
Case conversion may be inaccurate. Consider using '#align summable.update Summable.updateₓ'. -/
theorem Summable.update (hf : Summable f) (b : β) [DecidableEq β] (a : α) :
    Summable (update f b a) :=
  (hf.HasSum.update b a).Summable
#align summable.update Summable.update

/- warning: has_sum.has_sum_compl_iff -> HasSum.hasSum_compl_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {a₁ : α} {a₂ : α} {s : Set.{u2} β}, (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))))) a₁) -> (Iff (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)))))))) a₂) (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a₁ a₂)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {a₁ : α} {a₂ : α} {s : Set.{u2} β}, (HasSum.{u1, u2} α (Set.Elem.{u2} β s) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β s) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s))) a₁) -> (Iff (HasSum.{u1, u2} α (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)))) a₂) (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a₁ a₂)))
Case conversion may be inaccurate. Consider using '#align has_sum.has_sum_compl_iff HasSum.hasSum_compl_iffₓ'. -/
theorem HasSum.hasSum_compl_iff {s : Set β} (hf : HasSum (f ∘ coe : s → α) a₁) :
    HasSum (f ∘ coe : sᶜ → α) a₂ ↔ HasSum f (a₁ + a₂) :=
  by
  refine' ⟨fun h => hf.add_compl h, fun h => _⟩
  rw [hasSum_subtype_iff_indicator] at hf⊢
  rw [Set.indicator_compl]
  simpa only [add_sub_cancel'] using h.sub hf
#align has_sum.has_sum_compl_iff HasSum.hasSum_compl_iff

/- warning: has_sum.has_sum_iff_compl -> HasSum.hasSum_iff_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {a₁ : α} {a₂ : α} {s : Set.{u2} β}, (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))))) a₁) -> (Iff (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f a₂) (HasSum.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)))))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a₂ a₁)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {a₁ : α} {a₂ : α} {s : Set.{u2} β}, (HasSum.{u1, u2} α (Set.Elem.{u2} β s) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β s) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s))) a₁) -> (Iff (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f a₂) (HasSum.{u1, u2} α (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a₂ a₁)))
Case conversion may be inaccurate. Consider using '#align has_sum.has_sum_iff_compl HasSum.hasSum_iff_complₓ'. -/
theorem HasSum.hasSum_iff_compl {s : Set β} (hf : HasSum (f ∘ coe : s → α) a₁) :
    HasSum f a₂ ↔ HasSum (f ∘ coe : sᶜ → α) (a₂ - a₁) :=
  Iff.symm <| hf.hasSum_compl_iff.trans <| by rw [add_sub_cancel'_right]
#align has_sum.has_sum_iff_compl HasSum.hasSum_iff_compl

/- warning: summable.summable_compl_iff -> Summable.summable_compl_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {s : Set.{u2} β}, (Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s)))))))) -> (Iff (Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s))))))))) (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {s : Set.{u2} β}, (Summable.{u1, u2} α (Set.Elem.{u2} β s) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β s) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s)))) -> (Iff (Summable.{u1, u2} α (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s))))) (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f))
Case conversion may be inaccurate. Consider using '#align summable.summable_compl_iff Summable.summable_compl_iffₓ'. -/
theorem Summable.summable_compl_iff {s : Set β} (hf : Summable (f ∘ coe : s → α)) :
    Summable (f ∘ coe : sᶜ → α) ↔ Summable f :=
  ⟨fun ⟨a, ha⟩ => (hf.HasSum.hasSum_compl_iff.1 ha).Summable, fun ⟨a, ha⟩ =>
    (hf.HasSum.hasSum_iff_compl.1 ha).Summable⟩
#align summable.summable_compl_iff Summable.summable_compl_iff

/- warning: finset.has_sum_compl_iff -> Finset.hasSum_compl_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {a : α} (s : Finset.{u2} β), Iff (HasSum.{u1, u2} α (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (x : Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (HasLiftT.mk.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (CoeTCₓ.coe.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (coeBase.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (coeSubtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)))))) x)) a) (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (Finset.sum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) s (fun (i : β) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {a : α} (s : Finset.{u2} β), Iff (HasSum.{u1, u2} α (Subtype.{succ u2} β (fun (x : β) => Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s))) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (x : Subtype.{succ u2} β (fun (x : β) => Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s))) => f (Subtype.val.{succ u2} β (fun (x : β) => Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s)) x)) a) (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (Finset.sum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) s (fun (i : β) => f i))))
Case conversion may be inaccurate. Consider using '#align finset.has_sum_compl_iff Finset.hasSum_compl_iffₓ'. -/
protected theorem Finset.hasSum_compl_iff (s : Finset β) :
    HasSum (fun x : { x // x ∉ s } => f x) a ↔ HasSum f (a + ∑ i in s, f i) :=
  (s.HasSum f).hasSum_compl_iff.trans <| by rw [add_comm]
#align finset.has_sum_compl_iff Finset.hasSum_compl_iff

/- warning: finset.has_sum_iff_compl -> Finset.hasSum_iff_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {a : α} (s : Finset.{u2} β), Iff (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f a) (HasSum.{u1, u2} α (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (x : Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (HasLiftT.mk.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (CoeTCₓ.coe.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (coeBase.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (coeSubtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)))))) x)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a (Finset.sum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) s (fun (i : β) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {a : α} (s : Finset.{u2} β), Iff (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f a) (HasSum.{u1, u2} α (Subtype.{succ u2} β (fun (x : β) => Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s))) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (x : Subtype.{succ u2} β (fun (x : β) => Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s))) => f (Subtype.val.{succ u2} β (fun (x : β) => Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s)) x)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a (Finset.sum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) s (fun (i : β) => f i))))
Case conversion may be inaccurate. Consider using '#align finset.has_sum_iff_compl Finset.hasSum_iff_complₓ'. -/
protected theorem Finset.hasSum_iff_compl (s : Finset β) :
    HasSum f a ↔ HasSum (fun x : { x // x ∉ s } => f x) (a - ∑ i in s, f i) :=
  (s.HasSum f).hasSum_iff_compl
#align finset.has_sum_iff_compl Finset.hasSum_iff_compl

#print Finset.summable_compl_iff /-
protected theorem Finset.summable_compl_iff (s : Finset β) :
    (Summable fun x : { x // x ∉ s } => f x) ↔ Summable f :=
  (s.Summable f).summable_compl_iff
#align finset.summable_compl_iff Finset.summable_compl_iff
-/

/- warning: set.finite.summable_compl_iff -> Set.Finite.summable_compl_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {s : Set.{u2} β}, (Set.Finite.{u2} β s) -> (Iff (Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s))))))))) (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {s : Set.{u2} β}, (Set.Finite.{u2} β s) -> (Iff (Summable.{u1, u2} α (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) β α f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s))))) (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f))
Case conversion may be inaccurate. Consider using '#align set.finite.summable_compl_iff Set.Finite.summable_compl_iffₓ'. -/
theorem Set.Finite.summable_compl_iff {s : Set β} (hs : s.Finite) :
    Summable (f ∘ coe : sᶜ → α) ↔ Summable f :=
  (hs.Summable f).summable_compl_iff
#align set.finite.summable_compl_iff Set.Finite.summable_compl_iff

/- warning: has_sum_ite_sub_has_sum -> hasSum_ite_sub_hasSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {a : α} [_inst_4 : DecidableEq.{succ u2} β], (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f a) -> (forall (b : β), HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (n : β) => ite.{succ u1} α (Eq.{succ u2} β n b) (_inst_4 n b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))))) (f n)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a (f b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {a : α} [_inst_4 : DecidableEq.{succ u2} β], (HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f a) -> (forall (b : β), HasSum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (n : β) => ite.{succ u1} α (Eq.{succ u2} β n b) (_inst_4 n b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))))) (f n)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a (f b)))
Case conversion may be inaccurate. Consider using '#align has_sum_ite_sub_has_sum hasSum_ite_sub_hasSumₓ'. -/
theorem hasSum_ite_sub_hasSum [DecidableEq β] (hf : HasSum f a) (b : β) :
    HasSum (fun n => ite (n = b) 0 (f n)) (a - f b) :=
  by
  convert hf.update b 0 using 1
  · ext n
    rw [Function.update_apply]
  · rw [sub_add_eq_add_sub, zero_add]
#align has_sum_ite_sub_has_sum hasSum_ite_sub_hasSum

section tsum

variable [T2Space α]

/- warning: tsum_neg -> tsum_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} [_inst_4 : T2Space.{u1} α _inst_2], Eq.{succ u1} α (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 β (fun (b : β) => Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) (f b))) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 β (fun (b : β) => f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α} [_inst_4 : T2Space.{u2} α _inst_2], Eq.{succ u2} α (tsum.{u2, u1} α (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 β (fun (b : β) => Neg.neg.{u2} α (NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α _inst_1))))) (f b))) (Neg.neg.{u2} α (NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α _inst_1))))) (tsum.{u2, u1} α (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 β (fun (b : β) => f b)))
Case conversion may be inaccurate. Consider using '#align tsum_neg tsum_negₓ'. -/
theorem tsum_neg : (∑' b, -f b) = -∑' b, f b :=
  by
  by_cases hf : Summable f
  · exact hf.has_sum.neg.tsum_eq
  · simp [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt Summable.of_neg hf)]
#align tsum_neg tsum_neg

/- warning: tsum_sub -> tsum_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {g : β -> α} [_inst_4 : T2Space.{u1} α _inst_2], (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f) -> (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 g) -> (Eq.{succ u1} α (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 β (fun (b : β) => HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) (f b) (g b))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 β (fun (b : β) => f b)) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 β (fun (b : β) => g b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α} {g : β -> α} [_inst_4 : T2Space.{u2} α _inst_2], (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 g) -> (Eq.{succ u2} α (tsum.{u2, u1} α (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 β (fun (b : β) => HSub.hSub.{u2, u2, u2} α α α (instHSub.{u2} α (SubNegMonoid.toSub.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α _inst_1)))) (f b) (g b))) (HSub.hSub.{u2, u2, u2} α α α (instHSub.{u2} α (SubNegMonoid.toSub.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α _inst_1)))) (tsum.{u2, u1} α (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 β (fun (b : β) => f b)) (tsum.{u2, u1} α (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) _inst_2 β (fun (b : β) => g b))))
Case conversion may be inaccurate. Consider using '#align tsum_sub tsum_subₓ'. -/
theorem tsum_sub (hf : Summable f) (hg : Summable g) :
    (∑' b, f b - g b) = (∑' b, f b) - ∑' b, g b :=
  (hf.HasSum.sub hg.HasSum).tsum_eq
#align tsum_sub tsum_sub

/- warning: sum_add_tsum_compl -> sum_add_tsum_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} [_inst_4 : T2Space.{u1} α _inst_2] {s : Finset.{u2} β}, (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (Finset.sum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) s (fun (x : β) => f x)) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s))) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s))) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s))) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s))) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s))) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s))) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s))))))) x)))) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 β (fun (x : β) => f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} [_inst_4 : T2Space.{u1} α _inst_2] {s : Finset.{u2} β}, (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (Finset.sum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) s (fun (x : β) => f x)) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (Finset.toSet.{u2} β s))) (fun (x : Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (Finset.toSet.{u2} β s))) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (Finset.toSet.{u2} β s))) x)))) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 β (fun (x : β) => f x)))
Case conversion may be inaccurate. Consider using '#align sum_add_tsum_compl sum_add_tsum_complₓ'. -/
theorem sum_add_tsum_compl {s : Finset β} (hf : Summable f) :
    ((∑ x in s, f x) + ∑' x : (↑s : Set β)ᶜ, f x) = ∑' x, f x :=
  ((s.HasSum f).add_compl (s.summable_compl_iff.2 hf).HasSum).tsum_eq.symm
#align sum_add_tsum_compl sum_add_tsum_compl

/- warning: tsum_eq_add_tsum_ite -> tsum_eq_add_tsum_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} [_inst_4 : T2Space.{u1} α _inst_2] [_inst_5 : DecidableEq.{succ u2} β], (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f) -> (forall (b : β), Eq.{succ u1} α (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 β (fun (n : β) => f n)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (f b) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 β (fun (n : β) => ite.{succ u1} α (Eq.{succ u2} β n b) (_inst_5 n b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))))) (f n)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} [_inst_4 : T2Space.{u1} α _inst_2] [_inst_5 : DecidableEq.{succ u2} β], (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f) -> (forall (b : β), Eq.{succ u1} α (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 β (fun (n : β) => f n)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (f b) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 β (fun (n : β) => ite.{succ u1} α (Eq.{succ u2} β n b) (_inst_5 n b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))))) (f n)))))
Case conversion may be inaccurate. Consider using '#align tsum_eq_add_tsum_ite tsum_eq_add_tsum_iteₓ'. -/
/-- Let `f : β → α` be a sequence with summable series and let `b ∈ β` be an index.
Lemma `tsum_eq_add_tsum_ite` writes `Σ f n` as the sum of `f b` plus the series of the
remaining terms. -/
theorem tsum_eq_add_tsum_ite [DecidableEq β] (hf : Summable f) (b : β) :
    (∑' n, f n) = f b + ∑' n, ite (n = b) 0 (f n) :=
  by
  rw [(hasSum_ite_sub_hasSum hf.has_sum b).tsum_eq]
  exact (add_sub_cancel'_right _ _).symm
#align tsum_eq_add_tsum_ite tsum_eq_add_tsum_ite

end tsum

/-!
### Sums on nat

We show the formula `(∑ i in range k, f i) + (∑' i, f (i + k)) = (∑' i, f i)`, in
`sum_add_tsum_nat_add`, as well as several results relating sums on `ℕ` and `ℤ`.
-/


section Nat

/- warning: has_sum_nat_add_iff -> hasSum_nat_add_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : Nat -> α} (k : Nat) {a : α}, Iff (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n k)) a) (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (Finset.range k) (fun (i : Nat) => f i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : Nat -> α} (k : Nat) {a : α}, Iff (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n k)) a) (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (Finset.range k) (fun (i : Nat) => f i))))
Case conversion may be inaccurate. Consider using '#align has_sum_nat_add_iff hasSum_nat_add_iffₓ'. -/
theorem hasSum_nat_add_iff {f : ℕ → α} (k : ℕ) {a : α} :
    HasSum (fun n => f (n + k)) a ↔ HasSum f (a + ∑ i in range k, f i) :=
  by
  refine' Iff.trans _ (range k).hasSum_compl_iff
  rw [← (notMemRangeEquiv k).symm.hasSum_iff]
  rfl
#align has_sum_nat_add_iff hasSum_nat_add_iff

#print summable_nat_add_iff /-
theorem summable_nat_add_iff {f : ℕ → α} (k : ℕ) : (Summable fun n => f (n + k)) ↔ Summable f :=
  Iff.symm <|
    (Equiv.addRight (∑ i in range k, f i)).Surjective.summable_iff_of_hasSum_iff fun a =>
      (hasSum_nat_add_iff k).symm
#align summable_nat_add_iff summable_nat_add_iff
-/

/- warning: has_sum_nat_add_iff' -> hasSum_nat_add_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : Nat -> α} (k : Nat) {a : α}, Iff (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n k)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (Finset.range k) (fun (i : Nat) => f i)))) (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : Nat -> α} (k : Nat) {a : α}, Iff (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n k)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))) a (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (Finset.range k) (fun (i : Nat) => f i)))) (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f a)
Case conversion may be inaccurate. Consider using '#align has_sum_nat_add_iff' hasSum_nat_add_iff'ₓ'. -/
theorem hasSum_nat_add_iff' {f : ℕ → α} (k : ℕ) {a : α} :
    HasSum (fun n => f (n + k)) (a - ∑ i in range k, f i) ↔ HasSum f a := by
  simp [hasSum_nat_add_iff]
#align has_sum_nat_add_iff' hasSum_nat_add_iff'

/- warning: sum_add_tsum_nat_add -> sum_add_tsum_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] [_inst_4 : T2Space.{u1} α _inst_2] {f : Nat -> α} (k : Nat), (Summable.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (Finset.range k) (fun (i : Nat) => f i)) (tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 Nat (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i k)))) (tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 Nat (fun (i : Nat) => f i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] [_inst_4 : T2Space.{u1} α _inst_2] {f : Nat -> α} (k : Nat), (Summable.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (Finset.range k) (fun (i : Nat) => f i)) (tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 Nat (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i k)))) (tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 Nat (fun (i : Nat) => f i)))
Case conversion may be inaccurate. Consider using '#align sum_add_tsum_nat_add sum_add_tsum_nat_addₓ'. -/
theorem sum_add_tsum_nat_add [T2Space α] {f : ℕ → α} (k : ℕ) (h : Summable f) :
    ((∑ i in range k, f i) + ∑' i, f (i + k)) = ∑' i, f i := by
  simpa only [add_comm] using
    ((hasSum_nat_add_iff k).1 ((summable_nat_add_iff k).2 h).HasSum).unique h.has_sum
#align sum_add_tsum_nat_add sum_add_tsum_nat_add

/- warning: tsum_eq_zero_add -> tsum_eq_zero_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] [_inst_4 : T2Space.{u1} α _inst_2] {f : Nat -> α}, (Summable.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f) -> (Eq.{succ u1} α (tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 Nat (fun (b : Nat) => f b)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 Nat (fun (b : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) b (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] [_inst_4 : T2Space.{u1} α _inst_2] {f : Nat -> α}, (Summable.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f) -> (Eq.{succ u1} α (tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 Nat (fun (b : Nat) => f b)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 Nat (fun (b : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) b (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align tsum_eq_zero_add tsum_eq_zero_addₓ'. -/
theorem tsum_eq_zero_add [T2Space α] {f : ℕ → α} (hf : Summable f) :
    (∑' b, f b) = f 0 + ∑' b, f (b + 1) := by
  simpa only [sum_range_one] using (sum_add_tsum_nat_add 1 hf).symm
#align tsum_eq_zero_add tsum_eq_zero_add

/- warning: tendsto_sum_nat_add -> tendsto_sum_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] [_inst_4 : T2Space.{u1} α _inst_2] (f : Nat -> α), Filter.Tendsto.{0, u1} Nat α (fun (i : Nat) => tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 Nat (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} α _inst_2 (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] [_inst_4 : T2Space.{u1} α _inst_2] (f : Nat -> α), Filter.Tendsto.{0, u1} Nat α (fun (i : Nat) => tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 Nat (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} α _inst_2 (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align tendsto_sum_nat_add tendsto_sum_nat_addₓ'. -/
/-- For `f : ℕ → α`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
theorem tendsto_sum_nat_add [T2Space α] (f : ℕ → α) :
    Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) :=
  by
  by_cases hf : Summable f
  · have h₀ : (fun i => (∑' i, f i) - ∑ j in range i, f j) = fun i => ∑' k : ℕ, f (k + i) :=
      by
      ext1 i
      rw [sub_eq_iff_eq_add, add_comm, sum_add_tsum_nat_add i hf]
    have h₁ : tendsto (fun i : ℕ => ∑' i, f i) at_top (𝓝 (∑' i, f i)) := tendsto_const_nhds
    simpa only [h₀, sub_self] using tendsto.sub h₁ hf.has_sum.tendsto_sum_nat
  · convert tendsto_const_nhds
    ext1 i
    rw [← summable_nat_add_iff i] at hf
    · exact tsum_eq_zero_of_not_summable hf
    · infer_instance
#align tendsto_sum_nat_add tendsto_sum_nat_add

/- warning: has_sum.int_rec -> HasSum.int_rec is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {a : α} {b : α} {f : Nat -> α} {g : Nat -> α}, (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f a) -> (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 g b) -> (HasSum.{u1, 0} α Int (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Int.rec.{succ u1} (fun (_x : Int) => α) f g) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {a : α} {b : α} {f : Nat -> α} {g : Nat -> α}, (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f a) -> (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 g b) -> (HasSum.{u1, 0} α Int (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (Int.rec.{succ u1} (fun (_x : Int) => α) f g) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b))
Case conversion may be inaccurate. Consider using '#align has_sum.int_rec HasSum.int_recₓ'. -/
/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both convergent then so is the `ℤ`-indexed
sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...`. -/
theorem HasSum.int_rec {b : α} {f g : ℕ → α} (hf : HasSum f a) (hg : HasSum g b) :
    @HasSum α _ _ _ (@Int.rec (fun _ => α) f g : ℤ → α) (a + b) :=
  by
  -- note this proof works for any two-case inductive
  have h₁ : injective (coe : ℕ → ℤ) := @Int.ofNat.inj
  have h₂ : injective Int.negSucc := @Int.negSucc.inj
  have : IsCompl (Set.range (coe : ℕ → ℤ)) (Set.range Int.negSucc) :=
    by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) h
      exacts[Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]
  exact HasSum.add_isCompl this (h₁.has_sum_range_iff.mpr hf) (h₂.has_sum_range_iff.mpr hg)
#align has_sum.int_rec HasSum.int_rec

/- warning: has_sum.nonneg_add_neg -> HasSum.nonneg_add_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {a : α} {b : α} {f : Int -> α}, (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (n : Nat) => f ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)) a) -> (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (n : Nat) => f (Neg.neg.{0} Int Int.hasNeg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Nat.succ n)))) b) -> (HasSum.{u1, 0} α Int (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {a : α} {b : α} {f : Int -> α}, (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (n : Nat) => f (Nat.cast.{0} Int Int.instNatCastInt n)) a) -> (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (n : Nat) => f (Neg.neg.{0} Int Int.instNegInt (Nat.cast.{0} Int Int.instNatCastInt (Nat.succ n)))) b) -> (HasSum.{u1, 0} α Int (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a b))
Case conversion may be inaccurate. Consider using '#align has_sum.nonneg_add_neg HasSum.nonneg_add_negₓ'. -/
theorem HasSum.nonneg_add_neg {b : α} {f : ℤ → α} (hnonneg : HasSum (fun n : ℕ => f n) a)
    (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + b) :=
  by
  simp_rw [← Int.negSucc_coe] at hneg
  convert hnonneg.int_rec hneg using 1
  ext (i | j) <;> rfl
#align has_sum.nonneg_add_neg HasSum.nonneg_add_neg

/- warning: has_sum.pos_add_zero_add_neg -> HasSum.pos_add_zero_add_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {a : α} {b : α} {f : Int -> α}, (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))) a) -> (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (n : Nat) => f (Neg.neg.{0} Int Int.hasNeg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Nat.succ n)))) b) -> (HasSum.{u1, 0} α Int (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (f (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {a : α} {b : α} {f : Int -> α}, (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) (Nat.cast.{0} Int Int.instNatCastInt n) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))) a) -> (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 (fun (n : Nat) => f (Neg.neg.{0} Int Int.instNegInt (Nat.cast.{0} Int Int.instNatCastInt (Nat.succ n)))) b) -> (HasSum.{u1, 0} α Int (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_2 f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) a (f (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))) b))
Case conversion may be inaccurate. Consider using '#align has_sum.pos_add_zero_add_neg HasSum.pos_add_zero_add_negₓ'. -/
theorem HasSum.pos_add_zero_add_neg {b : α} {f : ℤ → α} (hpos : HasSum (fun n : ℕ => f (n + 1)) a)
    (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + f 0 + b) :=
  haveI : ∀ g : ℕ → α, HasSum (fun k => g (k + 1)) a → HasSum g (a + g 0) :=
    by
    intro g hg
    simpa using (hasSum_nat_add_iff _).mp hg
  (this (fun n => f n) hpos).nonneg_add_neg hneg
#align has_sum.pos_add_zero_add_neg HasSum.pos_add_zero_add_neg

#print summable_int_of_summable_nat /-
theorem summable_int_of_summable_nat {f : ℤ → α} (hp : Summable fun n : ℕ => f n)
    (hn : Summable fun n : ℕ => f (-n)) : Summable f :=
  (HasSum.nonneg_add_neg hp.HasSum <| Summable.hasSum <| (summable_nat_add_iff 1).mpr hn).Summable
#align summable_int_of_summable_nat summable_int_of_summable_nat
-/

/- warning: has_sum.sum_nat_of_sum_int -> HasSum.sum_nat_of_sum_int is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_4 : AddCommMonoid.{u1} α] [_inst_5 : TopologicalSpace.{u1} α] [_inst_6 : ContinuousAdd.{u1} α _inst_5 (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_4)))] {a : α} {f : Int -> α}, (HasSum.{u1, 0} α Int _inst_4 _inst_5 f a) -> (HasSum.{u1, 0} α Nat _inst_4 _inst_5 (fun (n : Nat) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_4)))) (f ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)) (f (Neg.neg.{0} Int Int.hasNeg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_4)))) a (f (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_4 : AddCommMonoid.{u1} α] [_inst_5 : TopologicalSpace.{u1} α] [_inst_6 : ContinuousAdd.{u1} α _inst_5 (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_4)))] {a : α} {f : Int -> α}, (HasSum.{u1, 0} α Int _inst_4 _inst_5 f a) -> (HasSum.{u1, 0} α Nat _inst_4 _inst_5 (fun (n : Nat) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_4)))) (f (Nat.cast.{0} Int Int.instNatCastInt n)) (f (Neg.neg.{0} Int Int.instNegInt (Nat.cast.{0} Int Int.instNatCastInt n)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_4)))) a (f (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))))
Case conversion may be inaccurate. Consider using '#align has_sum.sum_nat_of_sum_int HasSum.sum_nat_of_sum_intₓ'. -/
theorem HasSum.sum_nat_of_sum_int {α : Type _} [AddCommMonoid α] [TopologicalSpace α]
    [ContinuousAdd α] {a : α} {f : ℤ → α} (hf : HasSum f a) :
    HasSum (fun n : ℕ => f n + f (-n)) (a + f 0) :=
  by
  apply (hf.add (hasSum_ite_eq (0 : ℤ) (f 0))).hasSum_of_sum_eq fun u => _
  refine' ⟨u.image Int.natAbs, fun v' hv' => _⟩
  let u1 := v'.image fun x : ℕ => (x : ℤ)
  let u2 := v'.image fun x : ℕ => -(x : ℤ)
  have A : u ⊆ u1 ∪ u2 := by
    intro x hx
    simp only [mem_union, mem_image, exists_prop]
    rcases le_total 0 x with (h'x | h'x)
    · left
      refine' ⟨Int.natAbs x, hv' _, _⟩
      · simp only [mem_image, exists_prop]
        exact ⟨x, hx, rfl⟩
      · simp only [h'x, Int.coe_natAbs, abs_eq_self]
    · right
      refine' ⟨Int.natAbs x, hv' _, _⟩
      · simp only [mem_image, exists_prop]
        exact ⟨x, hx, rfl⟩
      · simp only [abs_of_nonpos h'x, Int.coe_natAbs, neg_neg]
  refine' ⟨u1 ∪ u2, A, _⟩
  calc
    (∑ x in u1 ∪ u2, f x + ite (x = 0) (f 0) 0) = (∑ x in u1 ∪ u2, f x) + ∑ x in u1 ∩ u2, f x :=
      by
      rw [sum_add_distrib]
      congr 1
      refine' (sum_subset_zero_on_sdiff inter_subset_union _ _).symm
      · intro x hx
        suffices x ≠ 0 by simp only [this, if_false]
        rintro rfl
        simpa only [mem_sdiff, mem_union, mem_image, neg_eq_zero, or_self_iff, mem_inter,
          and_self_iff, and_not_self_iff] using hx
      · intro x hx
        simp only [mem_inter, mem_image, exists_prop] at hx
        have : x = 0 := by
          apply le_antisymm
          · rcases hx.2 with ⟨a, ha, rfl⟩
            simp only [Right.neg_nonpos_iff, Nat.cast_nonneg]
          · rcases hx.1 with ⟨a, ha, rfl⟩
            simp only [Nat.cast_nonneg]
        simp only [this, eq_self_iff_true, if_true]
    _ = (∑ x in u1, f x) + ∑ x in u2, f x := sum_union_inter
    _ = (∑ b in v', f b) + ∑ b in v', f (-b) := by
      simp only [sum_image, Nat.cast_inj, imp_self, imp_true_iff, neg_inj]
    _ = ∑ b in v', f b + f (-b) := sum_add_distrib.symm
    
#align has_sum.sum_nat_of_sum_int HasSum.sum_nat_of_sum_int

end Nat

end TopologicalGroup

section UniformGroup

variable [AddCommGroup α] [UniformSpace α]

/- warning: summable_iff_cauchy_seq_finset -> summable_iff_cauchySeq_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : CompleteSpace.{u1} α _inst_2] {f : β -> α}, Iff (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) f) (CauchySeq.{u1, u2} α (Finset.{u2} β) _inst_2 (Lattice.toSemilatticeSup.{u2} (Finset.{u2} β) (Finset.lattice.{u2} β (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u2} β a b)))) (fun (s : Finset.{u2} β) => Finset.sum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) s (fun (b : β) => f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : UniformSpace.{u2} α] [_inst_3 : CompleteSpace.{u2} α _inst_2] {f : β -> α}, Iff (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) f) (CauchySeq.{u2, u1} α (Finset.{u1} β) _inst_2 (Lattice.toSemilatticeSup.{u1} (Finset.{u1} β) (Finset.instLatticeFinset.{u1} β (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u1} β a b)))) (fun (s : Finset.{u1} β) => Finset.sum.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) s (fun (b : β) => f b)))
Case conversion may be inaccurate. Consider using '#align summable_iff_cauchy_seq_finset summable_iff_cauchySeq_finsetₓ'. -/
/-- The **Cauchy criterion** for infinite sums, also known as the **Cauchy convergence test** -/
theorem summable_iff_cauchySeq_finset [CompleteSpace α] {f : β → α} :
    Summable f ↔ CauchySeq fun s : Finset β => ∑ b in s, f b :=
  cauchy_map_iff_exists_tendsto.symm
#align summable_iff_cauchy_seq_finset summable_iff_cauchySeq_finset

variable [UniformAddGroup α] {f g : β → α} {a a₁ a₂ : α}

/- warning: cauchy_seq_finset_iff_vanishing -> cauchySeq_finset_iff_vanishing is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α}, Iff (CauchySeq.{u1, u2} α (Finset.{u2} β) _inst_2 (Lattice.toSemilatticeSup.{u2} (Finset.{u2} β) (Finset.lattice.{u2} β (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u2} β a b)))) (fun (s : Finset.{u2} β) => Finset.sum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) s (fun (b : β) => f b))) (forall (e : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) e (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))))))) -> (Exists.{succ u2} (Finset.{u2} β) (fun (s : Finset.{u2} β) => forall (t : Finset.{u2} β), (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) t s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Finset.sum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) t (fun (b : β) => f b)) e))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : UniformSpace.{u2} α] [_inst_3 : UniformAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α}, Iff (CauchySeq.{u2, u1} α (Finset.{u1} β) _inst_2 (Lattice.toSemilatticeSup.{u1} (Finset.{u1} β) (Finset.instLatticeFinset.{u1} β (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u1} β a b)))) (fun (s : Finset.{u1} β) => Finset.sum.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) s (fun (b : β) => f b))) (forall (e : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) e (nhds.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_2) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (NegZeroClass.toZero.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α _inst_1))))))))) -> (Exists.{succ u1} (Finset.{u1} β) (fun (s : Finset.{u1} β) => forall (t : Finset.{u1} β), (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) t s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Finset.sum.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) t (fun (b : β) => f b)) e))))
Case conversion may be inaccurate. Consider using '#align cauchy_seq_finset_iff_vanishing cauchySeq_finset_iff_vanishingₓ'. -/
theorem cauchySeq_finset_iff_vanishing :
    (CauchySeq fun s : Finset β => ∑ b in s, f b) ↔
      ∀ e ∈ 𝓝 (0 : α), ∃ s : Finset β, ∀ t, Disjoint t s → (∑ b in t, f b) ∈ e :=
  by
  simp only [CauchySeq, cauchy_map_iff, and_iff_right at_top_ne_bot, prod_at_top_at_top_eq,
    uniformity_eq_comap_nhds_zero α, tendsto_comap_iff, (· ∘ ·)]
  rw [tendsto_at_top']
  constructor
  · intro h e he
    rcases h e he with ⟨⟨s₁, s₂⟩, h⟩
    use s₁ ∪ s₂
    intro t ht
    specialize h (s₁ ∪ s₂, s₁ ∪ s₂ ∪ t) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩
    simpa only [Finset.sum_union ht.symm, add_sub_cancel'] using h
  · intro h e he
    rcases exists_nhds_half_neg he with ⟨d, hd, hde⟩
    rcases h d hd with ⟨s, h⟩
    use (s, s)
    rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩
    have : ((∑ b in t₂, f b) - ∑ b in t₁, f b) = (∑ b in t₂ \ s, f b) - ∑ b in t₁ \ s, f b := by
      simp only [(Finset.sum_sdiff ht₁).symm, (Finset.sum_sdiff ht₂).symm, add_sub_add_right_eq_sub]
    simp only [this]
    exact hde _ (h _ Finset.sdiff_disjoint) _ (h _ Finset.sdiff_disjoint)
#align cauchy_seq_finset_iff_vanishing cauchySeq_finset_iff_vanishing

attribute [local instance] TopologicalAddGroup.t3Space

/- warning: tendsto_tsum_compl_at_top_zero -> tendsto_tsum_compl_atTop_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] (f : β -> α), Filter.Tendsto.{u2, u1} (Finset.{u2} β) α (fun (s : Finset.{u2} β) => tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) (fun (b : Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (HasLiftT.mk.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (CoeTCₓ.coe.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (coeBase.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (coeSubtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)))))) b))) (Filter.atTop.{u2} (Finset.{u2} β) (PartialOrder.toPreorder.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] (f : β -> α), Filter.Tendsto.{u2, u1} (Finset.{u2} β) α (fun (s : Finset.{u2} β) => tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (Subtype.{succ u2} β (fun (x : β) => Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s))) (fun (b : Subtype.{succ u2} β (fun (x : β) => Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s))) => f (Subtype.val.{succ u2} β (fun (x : β) => Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s)) b))) (Filter.atTop.{u2} (Finset.{u2} β) (PartialOrder.toPreorder.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align tendsto_tsum_compl_at_top_zero tendsto_tsum_compl_atTop_zeroₓ'. -/
/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
theorem tendsto_tsum_compl_atTop_zero (f : β → α) :
    Tendsto (fun s : Finset β => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) :=
  by
  by_cases H : Summable f
  · intro e he
    rcases exists_mem_nhds_isClosed_subset he with ⟨o, ho, o_closed, oe⟩
    simp only [le_eq_subset, Set.mem_preimage, mem_at_top_sets, Filter.mem_map, ge_iff_le]
    obtain ⟨s, hs⟩ : ∃ s : Finset β, ∀ t : Finset β, Disjoint t s → (∑ b : β in t, f b) ∈ o :=
      cauchySeq_finset_iff_vanishing.1 (tendsto.cauchy_seq H.has_sum) o ho
    refine' ⟨s, fun a sa => oe _⟩
    have A : Summable fun b : { x // x ∉ a } => f b := a.summable_compl_iff.2 H
    apply IsClosed.mem_of_tendsto o_closed A.has_sum (eventually_of_forall fun b => _)
    have : Disjoint (Finset.image (fun i : { x // x ∉ a } => (i : β)) b) s :=
      by
      apply disjoint_left.2 fun i hi his => _
      rcases mem_image.1 hi with ⟨i', hi', rfl⟩
      exact i'.2 (sa his)
    convert hs _ this using 1
    rw [sum_image]
    intro i hi j hj hij
    exact Subtype.ext hij
  · convert tendsto_const_nhds
    ext s
    apply tsum_eq_zero_of_not_summable
    rwa [Finset.summable_compl_iff]
#align tendsto_tsum_compl_at_top_zero tendsto_tsum_compl_atTop_zero

variable [CompleteSpace α]

/- warning: summable_iff_vanishing -> summable_iff_vanishing is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} [_inst_4 : CompleteSpace.{u1} α _inst_2], Iff (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) f) (forall (e : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) e (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))))))) -> (Exists.{succ u2} (Finset.{u2} β) (fun (s : Finset.{u2} β) => forall (t : Finset.{u2} β), (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) t s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Finset.sum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) t (fun (b : β) => f b)) e))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : UniformSpace.{u2} α] [_inst_3 : UniformAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α} [_inst_4 : CompleteSpace.{u2} α _inst_2], Iff (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) f) (forall (e : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) e (nhds.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_2) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (NegZeroClass.toZero.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α _inst_1))))))))) -> (Exists.{succ u1} (Finset.{u1} β) (fun (s : Finset.{u1} β) => forall (t : Finset.{u1} β), (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) t s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Finset.sum.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) t (fun (b : β) => f b)) e))))
Case conversion may be inaccurate. Consider using '#align summable_iff_vanishing summable_iff_vanishingₓ'. -/
theorem summable_iff_vanishing :
    Summable f ↔ ∀ e ∈ 𝓝 (0 : α), ∃ s : Finset β, ∀ t, Disjoint t s → (∑ b in t, f b) ∈ e := by
  rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_vanishing]
#align summable_iff_vanishing summable_iff_vanishing

/- warning: summable.summable_of_eq_zero_or_self -> Summable.summable_of_eq_zero_or_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} {g : β -> α} [_inst_4 : CompleteSpace.{u1} α _inst_2], (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) f) -> (forall (b : β), Or (Eq.{succ u1} α (g b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))))))) (Eq.{succ u1} α (g b) (f b))) -> (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : UniformSpace.{u2} α] [_inst_3 : UniformAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α} {g : β -> α} [_inst_4 : CompleteSpace.{u2} α _inst_2], (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) f) -> (forall (b : β), Or (Eq.{succ u2} α (g b) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (NegZeroClass.toZero.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α _inst_1)))))))) (Eq.{succ u2} α (g b) (f b))) -> (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) g)
Case conversion may be inaccurate. Consider using '#align summable.summable_of_eq_zero_or_self Summable.summable_of_eq_zero_or_selfₓ'. -/
-- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a`
theorem Summable.summable_of_eq_zero_or_self (hf : Summable f) (h : ∀ b, g b = 0 ∨ g b = f b) :
    Summable g :=
  summable_iff_vanishing.2 fun e he =>
    let ⟨s, hs⟩ := summable_iff_vanishing.1 hf e he
    ⟨s, fun t ht =>
      have eq : (∑ b in t.filterₓ fun b => g b = f b, f b) = ∑ b in t, g b :=
        calc
          (∑ b in t.filterₓ fun b => g b = f b, f b) = ∑ b in t.filterₓ fun b => g b = f b, g b :=
            Finset.sum_congr rfl fun b hb => (Finset.mem_filter.1 hb).2.symm
          _ = ∑ b in t, g b :=
            by
            refine' Finset.sum_subset (Finset.filter_subset _ _) _
            intro b hbt hb
            simp only [(· ∉ ·), Finset.mem_filter, and_iff_right hbt] at hb
            exact (h b).resolve_right hb
          
      Eq ▸ hs _ <| Finset.disjoint_of_subset_left (Finset.filter_subset _ _) ht⟩
#align summable.summable_of_eq_zero_or_self Summable.summable_of_eq_zero_or_self

/- warning: summable.indicator -> Summable.indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} [_inst_4 : CompleteSpace.{u1} α _inst_2], (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) f) -> (forall (s : Set.{u2} β), Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (Set.indicator.{u2, u1} β α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))))) s f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : UniformSpace.{u2} α] [_inst_3 : UniformAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α} [_inst_4 : CompleteSpace.{u2} α _inst_2], (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) f) -> (forall (s : Set.{u1} β), Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) (Set.indicator.{u1, u2} β α (NegZeroClass.toZero.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α _inst_1))))) s f))
Case conversion may be inaccurate. Consider using '#align summable.indicator Summable.indicatorₓ'. -/
protected theorem Summable.indicator (hf : Summable f) (s : Set β) : Summable (s.indicator f) :=
  hf.summable_of_eq_zero_or_self <| Set.indicator_eq_zero_or_self _ _
#align summable.indicator Summable.indicator

/- warning: summable.comp_injective -> Summable.comp_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} [_inst_4 : CompleteSpace.{u1} α _inst_2] {i : γ -> β}, (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) f) -> (Function.Injective.{succ u3, succ u2} γ β i) -> (Summable.{u1, u3} α γ (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (Function.comp.{succ u3, succ u2, succ u1} γ β α f i))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : AddCommGroup.{u3} α] [_inst_2 : UniformSpace.{u3} α] [_inst_3 : UniformAddGroup.{u3} α _inst_2 (AddCommGroup.toAddGroup.{u3} α _inst_1)] {f : β -> α} [_inst_4 : CompleteSpace.{u3} α _inst_2] {i : γ -> β}, (Summable.{u3, u2} α β (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} α _inst_2) f) -> (Function.Injective.{succ u1, succ u2} γ β i) -> (Summable.{u3, u1} α γ (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} α _inst_2) (Function.comp.{succ u1, succ u2, succ u3} γ β α f i))
Case conversion may be inaccurate. Consider using '#align summable.comp_injective Summable.comp_injectiveₓ'. -/
theorem Summable.comp_injective {i : γ → β} (hf : Summable f) (hi : Injective i) :
    Summable (f ∘ i) :=
  by
  simpa only [Set.indicator_range_comp] using (hi.summable_iff _).2 (hf.indicator (Set.range i))
  exact fun x hx => Set.indicator_of_not_mem hx _
#align summable.comp_injective Summable.comp_injective

/- warning: summable.subtype -> Summable.subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} [_inst_4 : CompleteSpace.{u1} α _inst_2], (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) f) -> (forall (s : Set.{u2} β), Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (Function.comp.{succ u2, succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : UniformSpace.{u2} α] [_inst_3 : UniformAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] {f : β -> α} [_inst_4 : CompleteSpace.{u2} α _inst_2], (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) f) -> (forall (s : Set.{u1} β), Summable.{u2, u1} α (Set.Elem.{u1} β s) (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) (Function.comp.{succ u1, succ u1, succ u2} (Set.Elem.{u1} β s) β α f (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x s))))
Case conversion may be inaccurate. Consider using '#align summable.subtype Summable.subtypeₓ'. -/
theorem Summable.subtype (hf : Summable f) (s : Set β) : Summable (f ∘ coe : s → α) :=
  hf.comp_injective Subtype.coe_injective
#align summable.subtype Summable.subtype

/- warning: summable_subtype_and_compl -> summable_subtype_and_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} [_inst_4 : CompleteSpace.{u1} α _inst_2] {s : Set.{u2} β}, Iff (And (Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) x))) (Summable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)))))) x)))) (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] {f : β -> α} [_inst_4 : CompleteSpace.{u1} α _inst_2] {s : Set.{u2} β}, Iff (And (Summable.{u1, u2} α (Set.Elem.{u2} β s) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (fun (x : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) x))) (Summable.{u1, u2} α (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (fun (x : Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) x)))) (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) f)
Case conversion may be inaccurate. Consider using '#align summable_subtype_and_compl summable_subtype_and_complₓ'. -/
theorem summable_subtype_and_compl {s : Set β} :
    ((Summable fun x : s => f x) ∧ Summable fun x : sᶜ => f x) ↔ Summable f :=
  ⟨and_imp.2 Summable.add_compl, fun h => ⟨h.Subtype s, h.Subtype (sᶜ)⟩⟩
#align summable_subtype_and_compl summable_subtype_and_compl

#print Summable.sigma_factor /-
theorem Summable.sigma_factor {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f) (b : β) :
    Summable fun c => f ⟨b, c⟩ :=
  ha.comp_injective sigma_mk_injective
#align summable.sigma_factor Summable.sigma_factor
-/

#print Summable.sigma /-
theorem Summable.sigma {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f) :
    Summable fun b => ∑' c, f ⟨b, c⟩ :=
  ha.sigma' fun b => ha.sigma_factor b
#align summable.sigma Summable.sigma
-/

/- warning: summable.prod_factor -> Summable.prod_factor is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] [_inst_4 : CompleteSpace.{u1} α _inst_2] {f : (Prod.{u2, u3} β γ) -> α}, (Summable.{u1, max u2 u3} α (Prod.{u2, u3} β γ) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) f) -> (forall (b : β), Summable.{u1, u3} α γ (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (fun (c : γ) => f (Prod.mk.{u2, u3} β γ b c)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] [_inst_4 : CompleteSpace.{u1} α _inst_2] {f : (Prod.{u3, u2} β γ) -> α}, (Summable.{u1, max u3 u2} α (Prod.{u3, u2} β γ) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) f) -> (forall (b : β), Summable.{u1, u2} α γ (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (fun (c : γ) => f (Prod.mk.{u3, u2} β γ b c)))
Case conversion may be inaccurate. Consider using '#align summable.prod_factor Summable.prod_factorₓ'. -/
theorem Summable.prod_factor {f : β × γ → α} (h : Summable f) (b : β) :
    Summable fun c => f (b, c) :=
  h.comp_injective fun c₁ c₂ h => (Prod.ext_iff.1 h).2
#align summable.prod_factor Summable.prod_factor

/- warning: tsum_sigma -> tsum_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] [_inst_4 : CompleteSpace.{u1} α _inst_2] [_inst_5 : T1Space.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_2)] {γ : β -> Type.{u3}} {f : (Sigma.{u2, u3} β (fun (b : β) => γ b)) -> α}, (Summable.{u1, max u2 u3} α (Sigma.{u2, u3} β (fun (b : β) => γ b)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) f) -> (Eq.{succ u1} α (tsum.{u1, max u2 u3} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (Sigma.{u2, u3} β (fun (b : β) => γ b)) (fun (p : Sigma.{u2, u3} β (fun (b : β) => γ b)) => f p)) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) β (fun (b : β) => tsum.{u1, u3} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (γ b) (fun (c : γ b) => f (Sigma.mk.{u2, u3} β (fun (b : β) => γ b) b c)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u3} α] [_inst_2 : UniformSpace.{u3} α] [_inst_3 : UniformAddGroup.{u3} α _inst_2 (AddCommGroup.toAddGroup.{u3} α _inst_1)] [_inst_4 : CompleteSpace.{u3} α _inst_2] [_inst_5 : T1Space.{u3} α (UniformSpace.toTopologicalSpace.{u3} α _inst_2)] {γ : β -> Type.{u2}} {f : (Sigma.{u1, u2} β (fun (b : β) => γ b)) -> α}, (Summable.{u3, max u1 u2} α (Sigma.{u1, u2} β (fun (b : β) => γ b)) (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} α _inst_2) f) -> (Eq.{succ u3} α (tsum.{u3, max u1 u2} α (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} α _inst_2) (Sigma.{u1, u2} β (fun (b : β) => γ b)) (fun (p : Sigma.{u1, u2} β (fun (b : β) => γ b)) => f p)) (tsum.{u3, u1} α (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} α _inst_2) β (fun (b : β) => tsum.{u3, u2} α (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} α _inst_2) (γ b) (fun (c : γ b) => f (Sigma.mk.{u1, u2} β (fun (b : β) => γ b) b c)))))
Case conversion may be inaccurate. Consider using '#align tsum_sigma tsum_sigmaₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
theorem tsum_sigma [T1Space α] {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f) :
    (∑' p, f p) = ∑' (b) (c), f ⟨b, c⟩ :=
  tsum_sigma' (fun b => ha.sigma_factor b) ha
#align tsum_sigma tsum_sigma

/- warning: tsum_prod -> tsum_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] [_inst_4 : CompleteSpace.{u1} α _inst_2] [_inst_5 : T1Space.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_2)] {f : (Prod.{u2, u3} β γ) -> α}, (Summable.{u1, max u2 u3} α (Prod.{u2, u3} β γ) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) f) -> (Eq.{succ u1} α (tsum.{u1, max u2 u3} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (Prod.{u2, u3} β γ) (fun (p : Prod.{u2, u3} β γ) => f p)) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) β (fun (b : β) => tsum.{u1, u3} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) γ (fun (c : γ) => f (Prod.mk.{u2, u3} β γ b c)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : AddCommGroup.{u3} α] [_inst_2 : UniformSpace.{u3} α] [_inst_3 : UniformAddGroup.{u3} α _inst_2 (AddCommGroup.toAddGroup.{u3} α _inst_1)] [_inst_4 : CompleteSpace.{u3} α _inst_2] [_inst_5 : T1Space.{u3} α (UniformSpace.toTopologicalSpace.{u3} α _inst_2)] {f : (Prod.{u2, u1} β γ) -> α}, (Summable.{u3, max u2 u1} α (Prod.{u2, u1} β γ) (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} α _inst_2) f) -> (Eq.{succ u3} α (tsum.{u3, max u2 u1} α (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} α _inst_2) (Prod.{u2, u1} β γ) (fun (p : Prod.{u2, u1} β γ) => f p)) (tsum.{u3, u2} α (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} α _inst_2) β (fun (b : β) => tsum.{u3, u1} α (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} α _inst_2) γ (fun (c : γ) => f (Prod.mk.{u2, u1} β γ b c)))))
Case conversion may be inaccurate. Consider using '#align tsum_prod tsum_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
theorem tsum_prod [T1Space α] {f : β × γ → α} (h : Summable f) :
    (∑' p, f p) = ∑' (b) (c), f ⟨b, c⟩ :=
  tsum_prod' h h.prod_factor
#align tsum_prod tsum_prod

/- warning: tsum_comm -> tsum_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] [_inst_4 : CompleteSpace.{u1} α _inst_2] [_inst_5 : T1Space.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_2)] {f : β -> γ -> α}, (Summable.{u1, max u2 u3} α (Prod.{u2, u3} β γ) (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (Function.uncurry.{u2, u3, u1} β γ α f)) -> (Eq.{succ u1} α (tsum.{u1, u3} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) γ (fun (c : γ) => tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) β (fun (b : β) => f b c))) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) β (fun (b : β) => tsum.{u1, u3} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) γ (fun (c : γ) => f b c))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : AddCommGroup.{u3} α] [_inst_2 : UniformSpace.{u3} α] [_inst_3 : UniformAddGroup.{u3} α _inst_2 (AddCommGroup.toAddGroup.{u3} α _inst_1)] [_inst_4 : CompleteSpace.{u3} α _inst_2] [_inst_5 : T1Space.{u3} α (UniformSpace.toTopologicalSpace.{u3} α _inst_2)] {f : β -> γ -> α}, (Summable.{u3, max u2 u1} α (Prod.{u1, u2} β γ) (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} α _inst_2) (Function.uncurry.{u1, u2, u3} β γ α f)) -> (Eq.{succ u3} α (tsum.{u3, u2} α (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} α _inst_2) γ (fun (c : γ) => tsum.{u3, u1} α (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} α _inst_2) β (fun (b : β) => f b c))) (tsum.{u3, u1} α (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} α _inst_2) β (fun (b : β) => tsum.{u3, u2} α (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) (UniformSpace.toTopologicalSpace.{u3} α _inst_2) γ (fun (c : γ) => f b c))))
Case conversion may be inaccurate. Consider using '#align tsum_comm tsum_commₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (c b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
theorem tsum_comm [T1Space α] {f : β → γ → α} (h : Summable (Function.uncurry f)) :
    (∑' (c) (b), f b c) = ∑' (b) (c), f b c :=
  tsum_comm' h h.prod_factor h.prod_symm.prod_factor
#align tsum_comm tsum_comm

/- warning: tsum_subtype_add_tsum_subtype_compl -> tsum_subtype_add_tsum_subtype_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] [_inst_4 : CompleteSpace.{u1} α _inst_2] [_inst_5 : T2Space.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_2)] {f : β -> α}, (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) f) -> (forall (s : Set.{u2} β), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) x))) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)))))) x)))) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) β (fun (x : β) => f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : UniformSpace.{u2} α] [_inst_3 : UniformAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] [_inst_4 : CompleteSpace.{u2} α _inst_2] [_inst_5 : T2Space.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_2)] {f : β -> α}, (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) f) -> (forall (s : Set.{u1} β), Eq.{succ u2} α (HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (SubNegMonoid.toAddMonoid.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α _inst_1)))))) (tsum.{u2, u1} α (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) (Set.Elem.{u1} β s) (fun (x : Set.Elem.{u1} β s) => f (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x s) x))) (tsum.{u2, u1} α (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) (Set.Elem.{u1} β (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) s)) (fun (x : Set.Elem.{u1} β (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) s)) => f (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) s)) x)))) (tsum.{u2, u1} α (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) β (fun (x : β) => f x)))
Case conversion may be inaccurate. Consider using '#align tsum_subtype_add_tsum_subtype_compl tsum_subtype_add_tsum_subtype_complₓ'. -/
theorem tsum_subtype_add_tsum_subtype_compl [T2Space α] {f : β → α} (hf : Summable f) (s : Set β) :
    ((∑' x : s, f x) + ∑' x : sᶜ, f x) = ∑' x, f x :=
  ((hf.Subtype s).HasSum.add_compl (hf.Subtype { x | x ∉ s }).HasSum).unique hf.HasSum
#align tsum_subtype_add_tsum_subtype_compl tsum_subtype_add_tsum_subtype_compl

/- warning: sum_add_tsum_subtype_compl -> sum_add_tsum_subtype_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : UniformSpace.{u1} α] [_inst_3 : UniformAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α _inst_1)] [_inst_4 : CompleteSpace.{u1} α _inst_2] [_inst_5 : T2Space.{u1} α (UniformSpace.toTopologicalSpace.{u1} α _inst_2)] {f : β -> α}, (Summable.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) f) -> (forall (s : Finset.{u2} β), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))))) (Finset.sum.{u1, u2} α β (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) s (fun (x : β) => f x)) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) (fun (x : Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (HasLiftT.mk.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (CoeTCₓ.coe.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (coeBase.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))) β (coeSubtype.{succ u2} β (fun (x : β) => Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)))))) x)))) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} α _inst_2) β (fun (x : β) => f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommGroup.{u2} α] [_inst_2 : UniformSpace.{u2} α] [_inst_3 : UniformAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α _inst_1)] [_inst_4 : CompleteSpace.{u2} α _inst_2] [_inst_5 : T2Space.{u2} α (UniformSpace.toTopologicalSpace.{u2} α _inst_2)] {f : β -> α}, (Summable.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) f) -> (forall (s : Finset.{u1} β), Eq.{succ u2} α (HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (SubNegMonoid.toAddMonoid.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α _inst_1)))))) (Finset.sum.{u2, u1} α β (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) s (fun (x : β) => f x)) (tsum.{u2, u1} α (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) (Subtype.{succ u1} β (fun (x : β) => Not (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x s))) (fun (x : Subtype.{succ u1} β (fun (x : β) => Not (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x s))) => f (Subtype.val.{succ u1} β (fun (x : β) => Not (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x s)) x)))) (tsum.{u2, u1} α (AddCommGroup.toAddCommMonoid.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) β (fun (x : β) => f x)))
Case conversion may be inaccurate. Consider using '#align sum_add_tsum_subtype_compl sum_add_tsum_subtype_complₓ'. -/
theorem sum_add_tsum_subtype_compl [T2Space α] {f : β → α} (hf : Summable f) (s : Finset β) :
    ((∑ x in s, f x) + ∑' x : { x // x ∉ s }, f x) = ∑' x, f x :=
  by
  rw [← tsum_subtype_add_tsum_subtype_compl hf s]
  simp only [Finset.tsum_subtype', add_right_inj]
  rfl
#align sum_add_tsum_subtype_compl sum_add_tsum_subtype_compl

end UniformGroup

section TopologicalGroup

variable {G : Type _} [TopologicalSpace G] [AddCommGroup G] [TopologicalAddGroup G] {f : α → G}

/- warning: summable.vanishing -> Summable.vanishing is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} G] [_inst_2 : AddCommGroup.{u2} G] [_inst_3 : TopologicalAddGroup.{u2} G _inst_1 (AddCommGroup.toAddGroup.{u2} G _inst_2)] {f : α -> G}, (Summable.{u2, u1} G α (AddCommGroup.toAddCommMonoid.{u2} G _inst_2) _inst_1 f) -> (forall {{e : Set.{u2} G}}, (Membership.Mem.{u2, u2} (Set.{u2} G) (Filter.{u2} G) (Filter.hasMem.{u2} G) e (nhds.{u2} G _inst_1 (OfNat.ofNat.{u2} G 0 (OfNat.mk.{u2} G 0 (Zero.zero.{u2} G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G _inst_2)))))))))) -> (Exists.{succ u1} (Finset.{u1} α) (fun (s : Finset.{u1} α) => forall (t : Finset.{u1} α), (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) t s) -> (Membership.Mem.{u2, u2} G (Set.{u2} G) (Set.hasMem.{u2} G) (Finset.sum.{u2, u1} G α (AddCommGroup.toAddCommMonoid.{u2} G _inst_2) t (fun (k : α) => f k)) e))))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} G] [_inst_2 : AddCommGroup.{u2} G] [_inst_3 : TopologicalAddGroup.{u2} G _inst_1 (AddCommGroup.toAddGroup.{u2} G _inst_2)] {f : α -> G}, (Summable.{u2, u1} G α (AddCommGroup.toAddCommMonoid.{u2} G _inst_2) _inst_1 f) -> (forall {{e : Set.{u2} G}}, (Membership.mem.{u2, u2} (Set.{u2} G) (Filter.{u2} G) (instMembershipSetFilter.{u2} G) e (nhds.{u2} G _inst_1 (OfNat.ofNat.{u2} G 0 (Zero.toOfNat0.{u2} G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (SubtractionCommMonoid.toSubtractionMonoid.{u2} G (AddCommGroup.toDivisionAddCommMonoid.{u2} G _inst_2))))))))) -> (Exists.{succ u1} (Finset.{u1} α) (fun (s : Finset.{u1} α) => forall (t : Finset.{u1} α), (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) t s) -> (Membership.mem.{u2, u2} G (Set.{u2} G) (Set.instMembershipSet.{u2} G) (Finset.sum.{u2, u1} G α (AddCommGroup.toAddCommMonoid.{u2} G _inst_2) t (fun (k : α) => f k)) e))))
Case conversion may be inaccurate. Consider using '#align summable.vanishing Summable.vanishingₓ'. -/
theorem Summable.vanishing (hf : Summable f) ⦃e : Set G⦄ (he : e ∈ 𝓝 (0 : G)) :
    ∃ s : Finset α, ∀ t, Disjoint t s → (∑ k in t, f k) ∈ e :=
  by
  letI : UniformSpace G := TopologicalAddGroup.toUniformSpace G
  letI : UniformAddGroup G := comm_topologicalAddGroup_is_uniform
  rcases hf with ⟨y, hy⟩
  exact cauchySeq_finset_iff_vanishing.1 hy.cauchy_seq e he
#align summable.vanishing Summable.vanishing

/- warning: summable.tendsto_cofinite_zero -> Summable.tendsto_cofinite_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} G] [_inst_2 : AddCommGroup.{u2} G] [_inst_3 : TopologicalAddGroup.{u2} G _inst_1 (AddCommGroup.toAddGroup.{u2} G _inst_2)] {f : α -> G}, (Summable.{u2, u1} G α (AddCommGroup.toAddCommMonoid.{u2} G _inst_2) _inst_1 f) -> (Filter.Tendsto.{u1, u2} α G f (Filter.cofinite.{u1} α) (nhds.{u2} G _inst_1 (OfNat.ofNat.{u2} G 0 (OfNat.mk.{u2} G 0 (Zero.zero.{u2} G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G _inst_2))))))))))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} G] [_inst_2 : AddCommGroup.{u2} G] [_inst_3 : TopologicalAddGroup.{u2} G _inst_1 (AddCommGroup.toAddGroup.{u2} G _inst_2)] {f : α -> G}, (Summable.{u2, u1} G α (AddCommGroup.toAddCommMonoid.{u2} G _inst_2) _inst_1 f) -> (Filter.Tendsto.{u1, u2} α G f (Filter.cofinite.{u1} α) (nhds.{u2} G _inst_1 (OfNat.ofNat.{u2} G 0 (Zero.toOfNat0.{u2} G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (SubtractionCommMonoid.toSubtractionMonoid.{u2} G (AddCommGroup.toDivisionAddCommMonoid.{u2} G _inst_2)))))))))
Case conversion may be inaccurate. Consider using '#align summable.tendsto_cofinite_zero Summable.tendsto_cofinite_zeroₓ'. -/
/-- Series divergence test: if `f` is a convergent series, then `f x` tends to zero along
`cofinite`. -/
theorem Summable.tendsto_cofinite_zero (hf : Summable f) : Tendsto f cofinite (𝓝 0) :=
  by
  intro e he
  rw [Filter.mem_map]
  rcases hf.vanishing he with ⟨s, hs⟩
  refine' s.eventually_cofinite_nmem.mono fun x hx => _
  · simpa using hs {x} (disjoint_singleton_left.2 hx)
#align summable.tendsto_cofinite_zero Summable.tendsto_cofinite_zero

/- warning: summable.tendsto_at_top_zero -> Summable.tendsto_atTop_zero is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : AddCommGroup.{u1} G] [_inst_3 : TopologicalAddGroup.{u1} G _inst_1 (AddCommGroup.toAddGroup.{u1} G _inst_2)] {f : Nat -> G}, (Summable.{u1, 0} G Nat (AddCommGroup.toAddCommMonoid.{u1} G _inst_2) _inst_1 f) -> (Filter.Tendsto.{0, u1} Nat G f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (AddZeroClass.toHasZero.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_2))))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} G] [_inst_2 : AddCommGroup.{u1} G] [_inst_3 : TopologicalAddGroup.{u1} G _inst_1 (AddCommGroup.toAddGroup.{u1} G _inst_2)] {f : Nat -> G}, (Summable.{u1, 0} G Nat (AddCommGroup.toAddCommMonoid.{u1} G _inst_2) _inst_1 f) -> (Filter.Tendsto.{0, u1} Nat G f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} G _inst_1 (OfNat.ofNat.{u1} G 0 (Zero.toOfNat0.{u1} G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G _inst_2)))))))))
Case conversion may be inaccurate. Consider using '#align summable.tendsto_at_top_zero Summable.tendsto_atTop_zeroₓ'. -/
theorem Summable.tendsto_atTop_zero {f : ℕ → G} (hf : Summable f) : Tendsto f atTop (𝓝 0) :=
  by
  rw [← Nat.cofinite_eq_atTop]
  exact hf.tendsto_cofinite_zero
#align summable.tendsto_at_top_zero Summable.tendsto_atTop_zero

end TopologicalGroup

section ConstSmul

variable [Monoid γ] [TopologicalSpace α] [AddCommMonoid α] [DistribMulAction γ α]
  [ContinuousConstSMul γ α] {f : β → α}

/- warning: has_sum.const_smul -> HasSum.const_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Monoid.{u3} γ] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : AddCommMonoid.{u1} α] [_inst_4 : DistribMulAction.{u3, u1} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u1} α _inst_3)] [_inst_5 : ContinuousConstSMul.{u3, u1} γ α _inst_2 (SMulZeroClass.toHasSmul.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3))) (DistribSMul.toSmulZeroClass.{u3, u1} γ α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3)) (DistribMulAction.toDistribSMul.{u3, u1} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u1} α _inst_3) _inst_4)))] {f : β -> α} {a : α} (b : γ), (HasSum.{u1, u2} α β _inst_3 _inst_2 f a) -> (HasSum.{u1, u2} α β _inst_3 _inst_2 (fun (i : β) => SMul.smul.{u3, u1} γ α (SMulZeroClass.toHasSmul.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3))) (DistribSMul.toSmulZeroClass.{u3, u1} γ α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3)) (DistribMulAction.toDistribSMul.{u3, u1} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u1} α _inst_3) _inst_4))) b (f i)) (SMul.smul.{u3, u1} γ α (SMulZeroClass.toHasSmul.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3))) (DistribSMul.toSmulZeroClass.{u3, u1} γ α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3)) (DistribMulAction.toDistribSMul.{u3, u1} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u1} α _inst_3) _inst_4))) b a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Monoid.{u1} γ] [_inst_2 : TopologicalSpace.{u3} α] [_inst_3 : AddCommMonoid.{u3} α] [_inst_4 : DistribMulAction.{u1, u3} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u3} α _inst_3)] [_inst_5 : ContinuousConstSMul.{u1, u3} γ α _inst_2 (SMulZeroClass.toSMul.{u1, u3} γ α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribSMul.toSMulZeroClass.{u1, u3} γ α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribMulAction.toDistribSMul.{u1, u3} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u3} α _inst_3) _inst_4)))] {f : β -> α} {a : α} (b : γ), (HasSum.{u3, u2} α β _inst_3 _inst_2 f a) -> (HasSum.{u3, u2} α β _inst_3 _inst_2 (fun (i : β) => HSMul.hSMul.{u1, u3, u3} γ α α (instHSMul.{u1, u3} γ α (SMulZeroClass.toSMul.{u1, u3} γ α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribSMul.toSMulZeroClass.{u1, u3} γ α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribMulAction.toDistribSMul.{u1, u3} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u3} α _inst_3) _inst_4)))) b (f i)) (HSMul.hSMul.{u1, u3, u3} γ α α (instHSMul.{u1, u3} γ α (SMulZeroClass.toSMul.{u1, u3} γ α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribSMul.toSMulZeroClass.{u1, u3} γ α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribMulAction.toDistribSMul.{u1, u3} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u3} α _inst_3) _inst_4)))) b a))
Case conversion may be inaccurate. Consider using '#align has_sum.const_smul HasSum.const_smulₓ'. -/
theorem HasSum.const_smul {a : α} (b : γ) (hf : HasSum f a) : HasSum (fun i => b • f i) (b • a) :=
  hf.map (DistribMulAction.toAddMonoidHom α _) <| continuous_const_smul _
#align has_sum.const_smul HasSum.const_smul

/- warning: summable.const_smul -> Summable.const_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Monoid.{u3} γ] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : AddCommMonoid.{u1} α] [_inst_4 : DistribMulAction.{u3, u1} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u1} α _inst_3)] [_inst_5 : ContinuousConstSMul.{u3, u1} γ α _inst_2 (SMulZeroClass.toHasSmul.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3))) (DistribSMul.toSmulZeroClass.{u3, u1} γ α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3)) (DistribMulAction.toDistribSMul.{u3, u1} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u1} α _inst_3) _inst_4)))] {f : β -> α} (b : γ), (Summable.{u1, u2} α β _inst_3 _inst_2 f) -> (Summable.{u1, u2} α β _inst_3 _inst_2 (fun (i : β) => SMul.smul.{u3, u1} γ α (SMulZeroClass.toHasSmul.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3))) (DistribSMul.toSmulZeroClass.{u3, u1} γ α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3)) (DistribMulAction.toDistribSMul.{u3, u1} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u1} α _inst_3) _inst_4))) b (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Monoid.{u1} γ] [_inst_2 : TopologicalSpace.{u3} α] [_inst_3 : AddCommMonoid.{u3} α] [_inst_4 : DistribMulAction.{u1, u3} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u3} α _inst_3)] [_inst_5 : ContinuousConstSMul.{u1, u3} γ α _inst_2 (SMulZeroClass.toSMul.{u1, u3} γ α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribSMul.toSMulZeroClass.{u1, u3} γ α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribMulAction.toDistribSMul.{u1, u3} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u3} α _inst_3) _inst_4)))] {f : β -> α} (b : γ), (Summable.{u3, u2} α β _inst_3 _inst_2 f) -> (Summable.{u3, u2} α β _inst_3 _inst_2 (fun (i : β) => HSMul.hSMul.{u1, u3, u3} γ α α (instHSMul.{u1, u3} γ α (SMulZeroClass.toSMul.{u1, u3} γ α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribSMul.toSMulZeroClass.{u1, u3} γ α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribMulAction.toDistribSMul.{u1, u3} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u3} α _inst_3) _inst_4)))) b (f i)))
Case conversion may be inaccurate. Consider using '#align summable.const_smul Summable.const_smulₓ'. -/
theorem Summable.const_smul (b : γ) (hf : Summable f) : Summable fun i => b • f i :=
  (hf.HasSum.const_smul _).Summable
#align summable.const_smul Summable.const_smul

/- warning: tsum_const_smul -> tsum_const_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Monoid.{u3} γ] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : AddCommMonoid.{u1} α] [_inst_4 : DistribMulAction.{u3, u1} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u1} α _inst_3)] [_inst_5 : ContinuousConstSMul.{u3, u1} γ α _inst_2 (SMulZeroClass.toHasSmul.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3))) (DistribSMul.toSmulZeroClass.{u3, u1} γ α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3)) (DistribMulAction.toDistribSMul.{u3, u1} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u1} α _inst_3) _inst_4)))] {f : β -> α} [_inst_6 : T2Space.{u1} α _inst_2] (b : γ), (Summable.{u1, u2} α β _inst_3 _inst_2 f) -> (Eq.{succ u1} α (tsum.{u1, u2} α _inst_3 _inst_2 β (fun (i : β) => SMul.smul.{u3, u1} γ α (SMulZeroClass.toHasSmul.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3))) (DistribSMul.toSmulZeroClass.{u3, u1} γ α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3)) (DistribMulAction.toDistribSMul.{u3, u1} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u1} α _inst_3) _inst_4))) b (f i))) (SMul.smul.{u3, u1} γ α (SMulZeroClass.toHasSmul.{u3, u1} γ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3))) (DistribSMul.toSmulZeroClass.{u3, u1} γ α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3)) (DistribMulAction.toDistribSMul.{u3, u1} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u1} α _inst_3) _inst_4))) b (tsum.{u1, u2} α _inst_3 _inst_2 β (fun (i : β) => f i))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Monoid.{u1} γ] [_inst_2 : TopologicalSpace.{u3} α] [_inst_3 : AddCommMonoid.{u3} α] [_inst_4 : DistribMulAction.{u1, u3} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u3} α _inst_3)] [_inst_5 : ContinuousConstSMul.{u1, u3} γ α _inst_2 (SMulZeroClass.toSMul.{u1, u3} γ α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribSMul.toSMulZeroClass.{u1, u3} γ α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribMulAction.toDistribSMul.{u1, u3} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u3} α _inst_3) _inst_4)))] {f : β -> α} [_inst_6 : T2Space.{u3} α _inst_2] (b : γ), (Summable.{u3, u2} α β _inst_3 _inst_2 f) -> (Eq.{succ u3} α (tsum.{u3, u2} α _inst_3 _inst_2 β (fun (i : β) => HSMul.hSMul.{u1, u3, u3} γ α α (instHSMul.{u1, u3} γ α (SMulZeroClass.toSMul.{u1, u3} γ α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribSMul.toSMulZeroClass.{u1, u3} γ α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribMulAction.toDistribSMul.{u1, u3} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u3} α _inst_3) _inst_4)))) b (f i))) (HSMul.hSMul.{u1, u3, u3} γ α α (instHSMul.{u1, u3} γ α (SMulZeroClass.toSMul.{u1, u3} γ α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribSMul.toSMulZeroClass.{u1, u3} γ α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_3)) (DistribMulAction.toDistribSMul.{u1, u3} γ α _inst_1 (AddCommMonoid.toAddMonoid.{u3} α _inst_3) _inst_4)))) b (tsum.{u3, u2} α _inst_3 _inst_2 β (fun (i : β) => f i))))
Case conversion may be inaccurate. Consider using '#align tsum_const_smul tsum_const_smulₓ'. -/
theorem tsum_const_smul [T2Space α] (b : γ) (hf : Summable f) : (∑' i, b • f i) = b • ∑' i, f i :=
  (hf.HasSum.const_smul _).tsum_eq
#align tsum_const_smul tsum_const_smul

end ConstSmul

/-! ### Product and pi types -/


section Prod

variable [AddCommMonoid α] [TopologicalSpace α] [AddCommMonoid γ] [TopologicalSpace γ]

/- warning: has_sum.prod_mk -> HasSum.prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : AddCommMonoid.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] {f : β -> α} {g : β -> γ} {a : α} {b : γ}, (HasSum.{u1, u2} α β _inst_1 _inst_2 f a) -> (HasSum.{u3, u2} γ β _inst_3 _inst_4 g b) -> (HasSum.{max u1 u3, u2} (Prod.{u1, u3} α γ) β (Prod.addCommMonoid.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u1, u3} α γ _inst_2 _inst_4) (fun (x : β) => Prod.mk.{u1, u3} α γ (f x) (g x)) (Prod.mk.{u1, u3} α γ a b))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : AddCommMonoid.{u3} α] [_inst_2 : TopologicalSpace.{u3} α] [_inst_3 : AddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] {f : β -> α} {g : β -> γ} {a : α} {b : γ}, (HasSum.{u3, u2} α β _inst_1 _inst_2 f a) -> (HasSum.{u1, u2} γ β _inst_3 _inst_4 g b) -> (HasSum.{max u3 u1, u2} (Prod.{u3, u1} α γ) β (Prod.instAddCommMonoidSum.{u3, u1} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u3, u1} α γ _inst_2 _inst_4) (fun (x : β) => Prod.mk.{u3, u1} α γ (f x) (g x)) (Prod.mk.{u3, u1} α γ a b))
Case conversion may be inaccurate. Consider using '#align has_sum.prod_mk HasSum.prod_mkₓ'. -/
theorem HasSum.prod_mk {f : β → α} {g : β → γ} {a : α} {b : γ} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun x => (⟨f x, g x⟩ : α × γ)) ⟨a, b⟩ := by
  simp [HasSum, ← prod_mk_sum, Filter.Tendsto.prod_mk_nhds hf hg]
#align has_sum.prod_mk HasSum.prod_mk

end Prod

section Pi

variable {ι : Type _} {π : α → Type _} [∀ x, AddCommMonoid (π x)] [∀ x, TopologicalSpace (π x)]

/- warning: pi.has_sum -> Pi.hasSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {π : α -> Type.{u3}} [_inst_1 : forall (x : α), AddCommMonoid.{u3} (π x)] [_inst_2 : forall (x : α), TopologicalSpace.{u3} (π x)] {f : ι -> (forall (x : α), π x)} {g : forall (x : α), π x}, Iff (HasSum.{max u1 u3, u2} (forall (x : α), π x) ι (Pi.addCommMonoid.{u1, u3} α (fun (x : α) => π x) (fun (i : α) => _inst_1 i)) (Pi.topologicalSpace.{u1, u3} α (fun (x : α) => π x) (fun (a : α) => _inst_2 a)) f g) (forall (x : α), HasSum.{u3, u2} (π x) ι (_inst_1 x) (_inst_2 x) (fun (i : ι) => f i x) (g x))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u1}} {π : α -> Type.{u2}} [_inst_1 : forall (x : α), AddCommMonoid.{u2} (π x)] [_inst_2 : forall (x : α), TopologicalSpace.{u2} (π x)] {f : ι -> (forall (x : α), π x)} {g : forall (x : α), π x}, Iff (HasSum.{max u3 u2, u1} (forall (x : α), π x) ι (Pi.addCommMonoid.{u3, u2} α (fun (x : α) => π x) (fun (i : α) => _inst_1 i)) (Pi.topologicalSpace.{u3, u2} α (fun (x : α) => π x) (fun (a : α) => _inst_2 a)) f g) (forall (x : α), HasSum.{u2, u1} (π x) ι (_inst_1 x) (_inst_2 x) (fun (i : ι) => f i x) (g x))
Case conversion may be inaccurate. Consider using '#align pi.has_sum Pi.hasSumₓ'. -/
theorem Pi.hasSum {f : ι → ∀ x, π x} {g : ∀ x, π x} :
    HasSum f g ↔ ∀ x, HasSum (fun i => f i x) (g x) := by
  simp only [HasSum, tendsto_pi_nhds, sum_apply]
#align pi.has_sum Pi.hasSum

/- warning: pi.summable -> Pi.summable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {π : α -> Type.{u3}} [_inst_1 : forall (x : α), AddCommMonoid.{u3} (π x)] [_inst_2 : forall (x : α), TopologicalSpace.{u3} (π x)] {f : ι -> (forall (x : α), π x)}, Iff (Summable.{max u1 u3, u2} (forall (x : α), π x) ι (Pi.addCommMonoid.{u1, u3} α (fun (x : α) => π x) (fun (i : α) => _inst_1 i)) (Pi.topologicalSpace.{u1, u3} α (fun (x : α) => π x) (fun (a : α) => _inst_2 a)) f) (forall (x : α), Summable.{u3, u2} (π x) ι (_inst_1 x) (_inst_2 x) (fun (i : ι) => f i x))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u1}} {π : α -> Type.{u2}} [_inst_1 : forall (x : α), AddCommMonoid.{u2} (π x)] [_inst_2 : forall (x : α), TopologicalSpace.{u2} (π x)] {f : ι -> (forall (x : α), π x)}, Iff (Summable.{max u3 u2, u1} (forall (x : α), π x) ι (Pi.addCommMonoid.{u3, u2} α (fun (x : α) => π x) (fun (i : α) => _inst_1 i)) (Pi.topologicalSpace.{u3, u2} α (fun (x : α) => π x) (fun (a : α) => _inst_2 a)) f) (forall (x : α), Summable.{u2, u1} (π x) ι (_inst_1 x) (_inst_2 x) (fun (i : ι) => f i x))
Case conversion may be inaccurate. Consider using '#align pi.summable Pi.summableₓ'. -/
theorem Pi.summable {f : ι → ∀ x, π x} : Summable f ↔ ∀ x, Summable fun i => f i x := by
  simp only [Summable, Pi.hasSum, skolem]
#align pi.summable Pi.summable

/- warning: tsum_apply -> tsum_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {π : α -> Type.{u3}} [_inst_1 : forall (x : α), AddCommMonoid.{u3} (π x)] [_inst_2 : forall (x : α), TopologicalSpace.{u3} (π x)] [_inst_3 : forall (x : α), T2Space.{u3} (π x) (_inst_2 x)] {f : ι -> (forall (x : α), π x)} {x : α}, (Summable.{max u1 u3, u2} (forall (x : α), π x) ι (Pi.addCommMonoid.{u1, u3} α (fun (x : α) => π x) (fun (i : α) => _inst_1 i)) (Pi.topologicalSpace.{u1, u3} α (fun (x : α) => π x) (fun (a : α) => _inst_2 a)) f) -> (Eq.{succ u3} (π x) (tsum.{max u1 u3, u2} (forall (x : α), π x) (Pi.addCommMonoid.{u1, u3} α (fun (x : α) => π x) (fun (i : α) => _inst_1 i)) (Pi.topologicalSpace.{u1, u3} α (fun (x : α) => π x) (fun (a : α) => _inst_2 a)) ι (fun (i : ι) => f i) x) (tsum.{u3, u2} (π x) (_inst_1 x) (_inst_2 x) ι (fun (i : ι) => f i x)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {π : α -> Type.{u3}} [_inst_1 : forall (x : α), AddCommMonoid.{u3} (π x)] [_inst_2 : forall (x : α), TopologicalSpace.{u3} (π x)] [_inst_3 : forall (x : α), T2Space.{u3} (π x) (_inst_2 x)] {f : ι -> (forall (x : α), π x)} {x : α}, (Summable.{max u2 u3, u1} (forall (x : α), π x) ι (Pi.addCommMonoid.{u2, u3} α (fun (x : α) => π x) (fun (i : α) => _inst_1 i)) (Pi.topologicalSpace.{u2, u3} α (fun (x : α) => π x) (fun (a : α) => _inst_2 a)) f) -> (Eq.{succ u3} (π x) (tsum.{max u2 u3, u1} (forall (x : α), π x) (Pi.addCommMonoid.{u2, u3} α (fun (x : α) => π x) (fun (i : α) => _inst_1 i)) (Pi.topologicalSpace.{u2, u3} α (fun (x : α) => π x) (fun (a : α) => _inst_2 a)) ι (fun (i : ι) => f i) x) (tsum.{u3, u1} (π x) (_inst_1 x) (_inst_2 x) ι (fun (i : ι) => f i x)))
Case conversion may be inaccurate. Consider using '#align tsum_apply tsum_applyₓ'. -/
theorem tsum_apply [∀ x, T2Space (π x)] {f : ι → ∀ x, π x} {x : α} (hf : Summable f) :
    (∑' i, f i) x = ∑' i, f i x :=
  (Pi.hasSum.mp hf.HasSum x).tsum_eq.symm
#align tsum_apply tsum_apply

end Pi

/-! ### Multiplicative opposite -/


section MulOpposite

open MulOpposite

variable [AddCommMonoid α] [TopologicalSpace α] {f : β → α} {a : α}

/- warning: has_sum.op -> HasSum.op is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α}, (HasSum.{u1, u2} α β _inst_1 _inst_2 f a) -> (HasSum.{u1, u2} (MulOpposite.{u1} α) β (MulOpposite.addCommMonoid.{u1} α _inst_1) (MulOpposite.topologicalSpace.{u1} α _inst_2) (fun (a : β) => MulOpposite.op.{u1} α (f a)) (MulOpposite.op.{u1} α a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α} {a : α}, (HasSum.{u2, u1} α β _inst_1 _inst_2 f a) -> (HasSum.{u2, u1} (MulOpposite.{u2} α) β (MulOpposite.instAddCommMonoidMulOpposite.{u2} α _inst_1) (MulOpposite.instTopologicalSpaceMulOpposite.{u2} α _inst_2) (fun (a : β) => MulOpposite.op.{u2} α (f a)) (MulOpposite.op.{u2} α a))
Case conversion may be inaccurate. Consider using '#align has_sum.op HasSum.opₓ'. -/
theorem HasSum.op (hf : HasSum f a) : HasSum (fun a => op (f a)) (op a) :=
  (hf.map (@opAddEquiv α _) continuous_op : _)
#align has_sum.op HasSum.op

/- warning: summable.op -> Summable.op is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α}, (Summable.{u1, u2} α β _inst_1 _inst_2 f) -> (Summable.{u1, u2} (MulOpposite.{u1} α) β (MulOpposite.addCommMonoid.{u1} α _inst_1) (MulOpposite.topologicalSpace.{u1} α _inst_2) (Function.comp.{succ u2, succ u1, succ u1} β α (MulOpposite.{u1} α) (MulOpposite.op.{u1} α) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α}, (Summable.{u2, u1} α β _inst_1 _inst_2 f) -> (Summable.{u2, u1} (MulOpposite.{u2} α) β (MulOpposite.instAddCommMonoidMulOpposite.{u2} α _inst_1) (MulOpposite.instTopologicalSpaceMulOpposite.{u2} α _inst_2) (Function.comp.{succ u1, succ u2, succ u2} β α (MulOpposite.{u2} α) (MulOpposite.op.{u2} α) f))
Case conversion may be inaccurate. Consider using '#align summable.op Summable.opₓ'. -/
theorem Summable.op (hf : Summable f) : Summable (op ∘ f) :=
  hf.HasSum.op.Summable
#align summable.op Summable.op

/- warning: has_sum.unop -> HasSum.unop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> (MulOpposite.{u1} α)} {a : MulOpposite.{u1} α}, (HasSum.{u1, u2} (MulOpposite.{u1} α) β (MulOpposite.addCommMonoid.{u1} α _inst_1) (MulOpposite.topologicalSpace.{u1} α _inst_2) f a) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 (fun (a : β) => MulOpposite.unop.{u1} α (f a)) (MulOpposite.unop.{u1} α a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> (MulOpposite.{u2} α)} {a : MulOpposite.{u2} α}, (HasSum.{u2, u1} (MulOpposite.{u2} α) β (MulOpposite.instAddCommMonoidMulOpposite.{u2} α _inst_1) (MulOpposite.instTopologicalSpaceMulOpposite.{u2} α _inst_2) f a) -> (HasSum.{u2, u1} α β _inst_1 _inst_2 (fun (a : β) => MulOpposite.unop.{u2} α (f a)) (MulOpposite.unop.{u2} α a))
Case conversion may be inaccurate. Consider using '#align has_sum.unop HasSum.unopₓ'. -/
theorem HasSum.unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : HasSum f a) :
    HasSum (fun a => unop (f a)) (unop a) :=
  (hf.map (@opAddEquiv α _).symm continuous_unop : _)
#align has_sum.unop HasSum.unop

/- warning: summable.unop -> Summable.unop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> (MulOpposite.{u1} α)}, (Summable.{u1, u2} (MulOpposite.{u1} α) β (MulOpposite.addCommMonoid.{u1} α _inst_1) (MulOpposite.topologicalSpace.{u1} α _inst_2) f) -> (Summable.{u1, u2} α β _inst_1 _inst_2 (Function.comp.{succ u2, succ u1, succ u1} β (MulOpposite.{u1} α) α (MulOpposite.unop.{u1} α) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> (MulOpposite.{u2} α)}, (Summable.{u2, u1} (MulOpposite.{u2} α) β (MulOpposite.instAddCommMonoidMulOpposite.{u2} α _inst_1) (MulOpposite.instTopologicalSpaceMulOpposite.{u2} α _inst_2) f) -> (Summable.{u2, u1} α β _inst_1 _inst_2 (Function.comp.{succ u1, succ u2, succ u2} β (MulOpposite.{u2} α) α (MulOpposite.unop.{u2} α) f))
Case conversion may be inaccurate. Consider using '#align summable.unop Summable.unopₓ'. -/
theorem Summable.unop {f : β → αᵐᵒᵖ} (hf : Summable f) : Summable (unop ∘ f) :=
  hf.HasSum.unop.Summable
#align summable.unop Summable.unop

/- warning: has_sum_op -> hasSum_op is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} {a : α}, Iff (HasSum.{u1, u2} (MulOpposite.{u1} α) β (MulOpposite.addCommMonoid.{u1} α _inst_1) (MulOpposite.topologicalSpace.{u1} α _inst_2) (fun (a : β) => MulOpposite.op.{u1} α (f a)) (MulOpposite.op.{u1} α a)) (HasSum.{u1, u2} α β _inst_1 _inst_2 f a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α} {a : α}, Iff (HasSum.{u2, u1} (MulOpposite.{u2} α) β (MulOpposite.instAddCommMonoidMulOpposite.{u2} α _inst_1) (MulOpposite.instTopologicalSpaceMulOpposite.{u2} α _inst_2) (fun (a : β) => MulOpposite.op.{u2} α (f a)) (MulOpposite.op.{u2} α a)) (HasSum.{u2, u1} α β _inst_1 _inst_2 f a)
Case conversion may be inaccurate. Consider using '#align has_sum_op hasSum_opₓ'. -/
@[simp]
theorem hasSum_op : HasSum (fun a => op (f a)) (op a) ↔ HasSum f a :=
  ⟨HasSum.unop, HasSum.op⟩
#align has_sum_op hasSum_op

/- warning: has_sum_unop -> hasSum_unop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> (MulOpposite.{u1} α)} {a : MulOpposite.{u1} α}, Iff (HasSum.{u1, u2} α β _inst_1 _inst_2 (fun (a : β) => MulOpposite.unop.{u1} α (f a)) (MulOpposite.unop.{u1} α a)) (HasSum.{u1, u2} (MulOpposite.{u1} α) β (MulOpposite.addCommMonoid.{u1} α _inst_1) (MulOpposite.topologicalSpace.{u1} α _inst_2) f a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> (MulOpposite.{u2} α)} {a : MulOpposite.{u2} α}, Iff (HasSum.{u2, u1} α β _inst_1 _inst_2 (fun (a : β) => MulOpposite.unop.{u2} α (f a)) (MulOpposite.unop.{u2} α a)) (HasSum.{u2, u1} (MulOpposite.{u2} α) β (MulOpposite.instAddCommMonoidMulOpposite.{u2} α _inst_1) (MulOpposite.instTopologicalSpaceMulOpposite.{u2} α _inst_2) f a)
Case conversion may be inaccurate. Consider using '#align has_sum_unop hasSum_unopₓ'. -/
@[simp]
theorem hasSum_unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} :
    HasSum (fun a => unop (f a)) (unop a) ↔ HasSum f a :=
  ⟨HasSum.op, HasSum.unop⟩
#align has_sum_unop hasSum_unop

/- warning: summable_op -> summable_op is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α}, Iff (Summable.{u1, u2} (MulOpposite.{u1} α) β (MulOpposite.addCommMonoid.{u1} α _inst_1) (MulOpposite.topologicalSpace.{u1} α _inst_2) (fun (a : β) => MulOpposite.op.{u1} α (f a))) (Summable.{u1, u2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α}, Iff (Summable.{u2, u1} (MulOpposite.{u2} α) β (MulOpposite.instAddCommMonoidMulOpposite.{u2} α _inst_1) (MulOpposite.instTopologicalSpaceMulOpposite.{u2} α _inst_2) (fun (a : β) => MulOpposite.op.{u2} α (f a))) (Summable.{u2, u1} α β _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align summable_op summable_opₓ'. -/
@[simp]
theorem summable_op : (Summable fun a => op (f a)) ↔ Summable f :=
  ⟨Summable.unop, Summable.op⟩
#align summable_op summable_op

/- warning: summable_unop -> summable_unop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> (MulOpposite.{u1} α)}, Iff (Summable.{u1, u2} α β _inst_1 _inst_2 (fun (a : β) => MulOpposite.unop.{u1} α (f a))) (Summable.{u1, u2} (MulOpposite.{u1} α) β (MulOpposite.addCommMonoid.{u1} α _inst_1) (MulOpposite.topologicalSpace.{u1} α _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> (MulOpposite.{u2} α)}, Iff (Summable.{u2, u1} α β _inst_1 _inst_2 (fun (a : β) => MulOpposite.unop.{u2} α (f a))) (Summable.{u2, u1} (MulOpposite.{u2} α) β (MulOpposite.instAddCommMonoidMulOpposite.{u2} α _inst_1) (MulOpposite.instTopologicalSpaceMulOpposite.{u2} α _inst_2) f)
Case conversion may be inaccurate. Consider using '#align summable_unop summable_unopₓ'. -/
@[simp]
theorem summable_unop {f : β → αᵐᵒᵖ} : (Summable fun a => unop (f a)) ↔ Summable f :=
  ⟨Summable.op, Summable.unop⟩
#align summable_unop summable_unop

variable [T2Space α]

/- warning: tsum_op -> tsum_op is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {f : β -> α} [_inst_3 : T2Space.{u1} α _inst_2], Eq.{succ u1} (MulOpposite.{u1} α) (tsum.{u1, u2} (MulOpposite.{u1} α) (MulOpposite.addCommMonoid.{u1} α _inst_1) (MulOpposite.topologicalSpace.{u1} α _inst_2) β (fun (x : β) => MulOpposite.op.{u1} α (f x))) (MulOpposite.op.{u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (x : β) => f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {f : β -> α} [_inst_3 : T2Space.{u2} α _inst_2], Eq.{succ u2} (MulOpposite.{u2} α) (tsum.{u2, u1} (MulOpposite.{u2} α) (MulOpposite.instAddCommMonoidMulOpposite.{u2} α _inst_1) (MulOpposite.instTopologicalSpaceMulOpposite.{u2} α _inst_2) β (fun (x : β) => MulOpposite.op.{u2} α (f x))) (MulOpposite.op.{u2} α (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (x : β) => f x)))
Case conversion may be inaccurate. Consider using '#align tsum_op tsum_opₓ'. -/
theorem tsum_op : (∑' x, MulOpposite.op (f x)) = MulOpposite.op (∑' x, f x) :=
  by
  by_cases h : Summable f
  · exact h.has_sum.op.tsum_eq
  · have ho := summable_op.not.mpr h
    rw [tsum_eq_zero_of_not_summable h, tsum_eq_zero_of_not_summable ho, MulOpposite.op_zero]
#align tsum_op tsum_op

/- warning: tsum_unop -> tsum_unop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_2] {f : β -> (MulOpposite.{u1} α)}, Eq.{succ u1} α (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (x : β) => MulOpposite.unop.{u1} α (f x))) (MulOpposite.unop.{u1} α (tsum.{u1, u2} (MulOpposite.{u1} α) (MulOpposite.addCommMonoid.{u1} α _inst_1) (MulOpposite.topologicalSpace.{u1} α _inst_2) β (fun (x : β) => f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : T2Space.{u2} α _inst_2] {f : β -> (MulOpposite.{u2} α)}, Eq.{succ u2} α (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (x : β) => MulOpposite.unop.{u2} α (f x))) (MulOpposite.unop.{u2} α (tsum.{u2, u1} (MulOpposite.{u2} α) (MulOpposite.instAddCommMonoidMulOpposite.{u2} α _inst_1) (MulOpposite.instTopologicalSpaceMulOpposite.{u2} α _inst_2) β (fun (x : β) => f x)))
Case conversion may be inaccurate. Consider using '#align tsum_unop tsum_unopₓ'. -/
theorem tsum_unop {f : β → αᵐᵒᵖ} : (∑' x, MulOpposite.unop (f x)) = MulOpposite.unop (∑' x, f x) :=
  MulOpposite.op_injective tsum_op.symm
#align tsum_unop tsum_unop

end MulOpposite

/-! ### Interaction with the star -/


section ContinuousStar

variable [AddCommMonoid α] [TopologicalSpace α] [StarAddMonoid α] [ContinuousStar α] {f : β → α}
  {a : α}

/- warning: has_sum.star -> HasSum.star is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : StarAddMonoid.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)] [_inst_4 : ContinuousStar.{u1} α _inst_2 (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_3))] {f : β -> α} {a : α}, (HasSum.{u1, u2} α β _inst_1 _inst_2 f a) -> (HasSum.{u1, u2} α β _inst_1 _inst_2 (fun (b : β) => Star.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_3)) (f b)) (Star.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_3)) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : StarAddMonoid.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)] [_inst_4 : ContinuousStar.{u2} α _inst_2 (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1) _inst_3))] {f : β -> α} {a : α}, (HasSum.{u2, u1} α β _inst_1 _inst_2 f a) -> (HasSum.{u2, u1} α β _inst_1 _inst_2 (fun (b : β) => Star.star.{u2} α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1) _inst_3)) (f b)) (Star.star.{u2} α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1) _inst_3)) a))
Case conversion may be inaccurate. Consider using '#align has_sum.star HasSum.starₓ'. -/
theorem HasSum.star (h : HasSum f a) : HasSum (fun b => star (f b)) (star a) := by
  simpa only using h.map (starAddEquiv : α ≃+ α) continuous_star
#align has_sum.star HasSum.star

/- warning: summable.star -> Summable.star is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : StarAddMonoid.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)] [_inst_4 : ContinuousStar.{u1} α _inst_2 (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_3))] {f : β -> α}, (Summable.{u1, u2} α β _inst_1 _inst_2 f) -> (Summable.{u1, u2} α β _inst_1 _inst_2 (fun (b : β) => Star.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_3)) (f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : StarAddMonoid.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)] [_inst_4 : ContinuousStar.{u2} α _inst_2 (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1) _inst_3))] {f : β -> α}, (Summable.{u2, u1} α β _inst_1 _inst_2 f) -> (Summable.{u2, u1} α β _inst_1 _inst_2 (fun (b : β) => Star.star.{u2} α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1) _inst_3)) (f b)))
Case conversion may be inaccurate. Consider using '#align summable.star Summable.starₓ'. -/
theorem Summable.star (hf : Summable f) : Summable fun b => star (f b) :=
  hf.HasSum.unit.Summable
#align summable.star Summable.star

/- warning: summable.of_star -> Summable.ofStar is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : StarAddMonoid.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)] [_inst_4 : ContinuousStar.{u1} α _inst_2 (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_3))] {f : β -> α}, (Summable.{u1, u2} α β _inst_1 _inst_2 (fun (b : β) => Star.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_3)) (f b))) -> (Summable.{u1, u2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : StarAddMonoid.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)] [_inst_4 : ContinuousStar.{u2} α _inst_2 (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1) _inst_3))] {f : β -> α}, (Summable.{u2, u1} α β _inst_1 _inst_2 (fun (b : β) => Star.star.{u2} α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1) _inst_3)) (f b))) -> (Summable.{u2, u1} α β _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align summable.of_star Summable.ofStarₓ'. -/
theorem Summable.ofStar (hf : Summable fun b => star (f b)) : Summable f := by
  simpa only [star_star] using hf.star
#align summable.of_star Summable.ofStar

/- warning: summable_star_iff -> summable_star_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : StarAddMonoid.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)] [_inst_4 : ContinuousStar.{u1} α _inst_2 (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_3))] {f : β -> α}, Iff (Summable.{u1, u2} α β _inst_1 _inst_2 (fun (b : β) => Star.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_3)) (f b))) (Summable.{u1, u2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : StarAddMonoid.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)] [_inst_4 : ContinuousStar.{u2} α _inst_2 (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1) _inst_3))] {f : β -> α}, Iff (Summable.{u2, u1} α β _inst_1 _inst_2 (fun (b : β) => Star.star.{u2} α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1) _inst_3)) (f b))) (Summable.{u2, u1} α β _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align summable_star_iff summable_star_iffₓ'. -/
@[simp]
theorem summable_star_iff : (Summable fun b => star (f b)) ↔ Summable f :=
  ⟨Summable.ofStar, Summable.star⟩
#align summable_star_iff summable_star_iff

/- warning: summable_star_iff' -> summable_star_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : StarAddMonoid.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)] [_inst_4 : ContinuousStar.{u1} α _inst_2 (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_3))] {f : β -> α}, Iff (Summable.{u1, u2} α β _inst_1 _inst_2 (Star.star.{max u2 u1} (β -> α) (Pi.hasStar.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_3))) f)) (Summable.{u1, u2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : StarAddMonoid.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)] [_inst_4 : ContinuousStar.{u2} α _inst_2 (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1) _inst_3))] {f : β -> α}, Iff (Summable.{u2, u1} α β _inst_1 _inst_2 (Star.star.{max u1 u2} (β -> α) (Pi.instStarForAll.{u1, u2} β (fun (ᾰ : β) => α) (fun (i : β) => InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1) _inst_3))) f)) (Summable.{u2, u1} α β _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align summable_star_iff' summable_star_iff'ₓ'. -/
@[simp]
theorem summable_star_iff' : Summable (star f) ↔ Summable f :=
  summable_star_iff
#align summable_star_iff' summable_star_iff'

variable [T2Space α]

/- warning: tsum_star -> tsum_star is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : StarAddMonoid.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)] [_inst_4 : ContinuousStar.{u1} α _inst_2 (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_3))] {f : β -> α} [_inst_5 : T2Space.{u1} α _inst_2], Eq.{succ u1} α (Star.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_3)) (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => f b))) (tsum.{u1, u2} α _inst_1 _inst_2 β (fun (b : β) => Star.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_3)) (f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : StarAddMonoid.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1)] [_inst_4 : ContinuousStar.{u2} α _inst_2 (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1) _inst_3))] {f : β -> α} [_inst_5 : T2Space.{u2} α _inst_2], Eq.{succ u2} α (Star.star.{u2} α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1) _inst_3)) (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => f b))) (tsum.{u2, u1} α _inst_1 _inst_2 β (fun (b : β) => Star.star.{u2} α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1) _inst_3)) (f b)))
Case conversion may be inaccurate. Consider using '#align tsum_star tsum_starₓ'. -/
theorem tsum_star : star (∑' b, f b) = ∑' b, star (f b) :=
  by
  by_cases hf : Summable f
  · exact hf.has_sum.star.tsum_eq.symm
  ·
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt Summable.ofStar hf),
      star_zero]
#align tsum_star tsum_star

end ContinuousStar

