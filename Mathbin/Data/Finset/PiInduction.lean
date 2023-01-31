/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.finset.pi_induction
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Lattice
import Mathbin.Data.Finset.Sigma

/-!
# Induction principles for `Π i, finset (α i)`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove a few induction principles for functions `Π i : ι, finset (α i)` defined on a
finite type.

* `finset.induction_on_pi` is a generic lemma that requires only `[finite ι]`, `[decidable_eq ι]`,
  and `[Π i, decidable_eq (α i)]`; this version can be seen as a direct generalization of
  `finset.induction_on`.

* `finset.induction_on_pi_max` and `finset.induction_on_pi_min`: generalizations of
  `finset.induction_on_max`; these versions require `Π i, linear_order (α i)` but assume
  `∀ y ∈ g i, y < x` and `∀ y ∈ g i, x < y` respectively in the induction step.

## Tags
finite set, finite type, induction, function
-/


open Function

variable {ι : Type _} {α : ι → Type _} [Finite ι] [DecidableEq ι] [∀ i, DecidableEq (α i)]

namespace Finset

/- warning: finset.induction_on_pi_of_choice -> Finset.induction_on_pi_of_choice is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : Finite.{succ u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u2} (α i)] (r : forall (i : ι), (α i) -> (Finset.{u2} (α i)) -> Prop), (forall (i : ι) (s : Finset.{u2} (α i)), (Finset.Nonempty.{u2} (α i) s) -> (Exists.{succ u2} (α i) (fun (x : α i) => Exists.{0} (Membership.Mem.{u2, u2} (α i) (Finset.{u2} (α i)) (Finset.hasMem.{u2} (α i)) x s) (fun (H : Membership.Mem.{u2, u2} (α i) (Finset.{u2} (α i)) (Finset.hasMem.{u2} (α i)) x s) => r i x (Finset.erase.{u2} (α i) (fun (a : α i) (b : α i) => _inst_3 i a b) s x))))) -> (forall {p : (forall (i : ι), Finset.{u2} (α i)) -> Prop} (f : forall (i : ι), Finset.{u2} (α i)), (p (fun (_x : ι) => EmptyCollection.emptyCollection.{u2} (Finset.{u2} (α _x)) (Finset.hasEmptyc.{u2} (α _x)))) -> (forall (g : forall (i : ι), Finset.{u2} (α i)) (i : ι) (x : α i), (r i x (g i)) -> (p g) -> (p (Function.update.{succ u1, succ u2} ι (fun (i : ι) => Finset.{u2} (α i)) (fun (a : ι) (b : ι) => _inst_2 a b) g i (Insert.insert.{u2, u2} (α i) (Finset.{u2} (α i)) (Finset.hasInsert.{u2} (α i) (fun (a : α i) (b : α i) => _inst_3 i a b)) x (g i))))) -> (p f))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : Finite.{succ u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u2} (α i)] (r : forall (i : ι), (α i) -> (Finset.{u2} (α i)) -> Prop), (forall (i : ι) (s : Finset.{u2} (α i)), (Finset.Nonempty.{u2} (α i) s) -> (Exists.{succ u2} (α i) (fun (x : α i) => And (Membership.mem.{u2, u2} (α i) (Finset.{u2} (α i)) (Finset.instMembershipFinset.{u2} (α i)) x s) (r i x (Finset.erase.{u2} (α i) (fun (a : α i) (b : α i) => _inst_3 i a b) s x))))) -> (forall {p : (forall (i : ι), Finset.{u2} (α i)) -> Prop} (f : forall (i : ι), Finset.{u2} (α i)), (p (fun (_x : ι) => EmptyCollection.emptyCollection.{u2} (Finset.{u2} (α _x)) (Finset.instEmptyCollectionFinset.{u2} (α _x)))) -> (forall (g : forall (i : ι), Finset.{u2} (α i)) (i : ι) (x : α i), (r i x (g i)) -> (p g) -> (p (Function.update.{succ u1, succ u2} ι (fun (i : ι) => Finset.{u2} (α i)) (fun (a : ι) (b : ι) => _inst_2 a b) g i (Insert.insert.{u2, u2} (α i) (Finset.{u2} (α i)) (Finset.instInsertFinset.{u2} (α i) (fun (a : α i) (b : α i) => _inst_3 i a b)) x (g i))))) -> (p f))
Case conversion may be inaccurate. Consider using '#align finset.induction_on_pi_of_choice Finset.induction_on_pi_of_choiceₓ'. -/
/-- General theorem for `finset.induction_on_pi`-style induction principles. -/
theorem induction_on_pi_of_choice (r : ∀ i, α i → Finset (α i) → Prop)
    (H_ex : ∀ (i) (s : Finset (α i)) (hs : s.Nonempty), ∃ x ∈ s, r i x (s.erase x))
    {p : (∀ i, Finset (α i)) → Prop} (f : ∀ i, Finset (α i)) (h0 : p fun _ => ∅)
    (step :
      ∀ (g : ∀ i, Finset (α i)) (i : ι) (x : α i),
        r i x (g i) → p g → p (update g i (insert x (g i)))) :
    p f := by
  cases nonempty_fintype ι
  induction' hs : univ.sigma f using Finset.strongInductionOn with s ihs generalizing f; subst s
  cases' eq_empty_or_nonempty (univ.sigma f) with he hne
  · convert h0
    simpa [funext_iff] using he
  · rcases sigma_nonempty.1 hne with ⟨i, -, hi⟩
    rcases H_ex i (f i) hi with ⟨x, x_mem, hr⟩
    set g := update f i ((f i).erase x) with hg
    clear_value g
    have hx' : x ∉ g i := by
      rw [hg, update_same]
      apply not_mem_erase
    obtain rfl : f = update g i (insert x (g i)) := by
      rw [hg, update_idem, update_same, insert_erase x_mem, update_eq_self]
    clear hg
    rw [update_same, erase_insert hx'] at hr
    refine' step _ _ _ hr (ihs (univ.sigma g) _ _ rfl)
    rw [ssubset_iff_of_subset (sigma_mono (subset.refl _) _)]
    exacts[⟨⟨i, x⟩, mem_sigma.2 ⟨mem_univ _, by simp⟩, by simp [hx']⟩,
      (@le_update_iff _ _ _ _ g g i _).2 ⟨subset_insert _ _, fun _ _ => le_rfl⟩]
#align finset.induction_on_pi_of_choice Finset.induction_on_pi_of_choice

#print Finset.induction_on_pi /-
/-- Given a predicate on functions `Π i, finset (α i)` defined on a finite type, it is true on all
maps provided that it is true on `λ _, ∅` and for any function `g : Π i, finset (α i)`, an index
`i : ι`, and `x ∉ g i`, `p g` implies `p (update g i (insert x (g i)))`.

See also `finset.induction_on_pi_max` and `finset.induction_on_pi_min` for specialized versions
that require `Π i, linear_order (α i)`.  -/
theorem induction_on_pi {p : (∀ i, Finset (α i)) → Prop} (f : ∀ i, Finset (α i)) (h0 : p fun _ => ∅)
    (step :
      ∀ (g : ∀ i, Finset (α i)) (i : ι) (x : α i) (hx : x ∉ g i),
        p g → p (update g i (insert x (g i)))) :
    p f :=
  induction_on_pi_of_choice (fun i x s => x ∉ s) (fun i s ⟨x, hx⟩ => ⟨x, hx, not_mem_erase x s⟩) f
    h0 step
#align finset.induction_on_pi Finset.induction_on_pi
-/

#print Finset.induction_on_pi_max /-
/-- Given a predicate on functions `Π i, finset (α i)` defined on a finite type, it is true on all
maps provided that it is true on `λ _, ∅` and for any function `g : Π i, finset (α i)`, an index
`i : ι`, and an element`x : α i` that is strictly greater than all elements of `g i`, `p g` implies
`p (update g i (insert x (g i)))`.

This lemma requires `linear_order` instances on all `α i`. See also `finset.induction_on_pi` for a
version that `x ∉ g i` instead of ` does not need `Π i, linear_order (α i)`. -/
theorem induction_on_pi_max [∀ i, LinearOrder (α i)] {p : (∀ i, Finset (α i)) → Prop}
    (f : ∀ i, Finset (α i)) (h0 : p fun _ => ∅)
    (step :
      ∀ (g : ∀ i, Finset (α i)) (i : ι) (x : α i),
        (∀ y ∈ g i, y < x) → p g → p (update g i (insert x (g i)))) :
    p f :=
  induction_on_pi_of_choice (fun i x s => ∀ y ∈ s, y < x)
    (fun i s hs => ⟨s.max' hs, s.max'_mem hs, fun y => s.lt_max'_of_mem_erase_max' _⟩) f h0 step
#align finset.induction_on_pi_max Finset.induction_on_pi_max
-/

#print Finset.induction_on_pi_min /-
/-- Given a predicate on functions `Π i, finset (α i)` defined on a finite type, it is true on all
maps provided that it is true on `λ _, ∅` and for any function `g : Π i, finset (α i)`, an index
`i : ι`, and an element`x : α i` that is strictly less than all elements of `g i`, `p g` implies
`p (update g i (insert x (g i)))`.

This lemma requires `linear_order` instances on all `α i`. See also `finset.induction_on_pi` for a
version that `x ∉ g i` instead of ` does not need `Π i, linear_order (α i)`. -/
theorem induction_on_pi_min [∀ i, LinearOrder (α i)] {p : (∀ i, Finset (α i)) → Prop}
    (f : ∀ i, Finset (α i)) (h0 : p fun _ => ∅)
    (step :
      ∀ (g : ∀ i, Finset (α i)) (i : ι) (x : α i),
        (∀ y ∈ g i, x < y) → p g → p (update g i (insert x (g i)))) :
    p f :=
  @induction_on_pi_max ι (fun i => (α i)ᵒᵈ) _ _ _ _ _ _ h0 step
#align finset.induction_on_pi_min Finset.induction_on_pi_min
-/

end Finset

