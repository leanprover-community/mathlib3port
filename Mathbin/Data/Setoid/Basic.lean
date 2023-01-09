/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen

! This file was ported from Lean 3 source module data.setoid.basic
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Relation
import Mathbin.Order.GaloisConnection

/-!
# Equivalence relations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the complete lattice of equivalence relations on a type, results about the
inductively defined equivalence closure of a binary relation, and the analogues of some isomorphism
theorems for quotients of arbitrary types.

## Implementation notes

The function `rel` and lemmas ending in ' make it easier to talk about different
equivalence relations on the same type.

The complete lattice instance for equivalence relations could have been defined by lifting
the Galois insertion of equivalence relations on α into binary relations on α, and then using
`complete_lattice.copy` to define a complete lattice instance with more appropriate
definitional equalities (a similar example is `filter.complete_lattice` in
`order/filter/basic.lean`). This does not save space, however, and is less clear.

Partitions are not defined as a separate structure here; users are encouraged to
reason about them using the existing `setoid` and its infrastructure.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation
-/


variable {α : Type _} {β : Type _}

#print Setoid.Rel /-
/-- A version of `setoid.r` that takes the equivalence relation as an explicit argument. -/
def Setoid.Rel (r : Setoid α) : α → α → Prop :=
  @Setoid.r _ r
#align setoid.rel Setoid.Rel
-/

#print Setoid.decidableRel /-
instance Setoid.decidableRel (r : Setoid α) [h : DecidableRel r.R] : DecidableRel r.Rel :=
  h
#align setoid.decidable_rel Setoid.decidableRel
-/

#print Quotient.eq_rel /-
/-- A version of `quotient.eq'` compatible with `setoid.rel`, to make rewriting possible. -/
theorem Quotient.eq_rel {r : Setoid α} {x y} :
    (Quotient.mk' x : Quotient r) = Quotient.mk' y ↔ r.Rel x y :=
  Quotient.eq
#align quotient.eq_rel Quotient.eq_rel
-/

namespace Setoid

#print Setoid.ext' /-
@[ext]
theorem ext' {r s : Setoid α} (H : ∀ a b, r.Rel a b ↔ s.Rel a b) : r = s :=
  ext H
#align setoid.ext' Setoid.ext'
-/

#print Setoid.ext_iff /-
theorem ext_iff {r s : Setoid α} : r = s ↔ ∀ a b, r.Rel a b ↔ s.Rel a b :=
  ⟨fun h a b => h ▸ Iff.rfl, ext'⟩
#align setoid.ext_iff Setoid.ext_iff
-/

#print Setoid.eq_iff_rel_eq /-
/-- Two equivalence relations are equal iff their underlying binary operations are equal. -/
theorem eq_iff_rel_eq {r₁ r₂ : Setoid α} : r₁ = r₂ ↔ r₁.Rel = r₂.Rel :=
  ⟨fun h => h ▸ rfl, fun h => Setoid.ext' fun x y => h ▸ Iff.rfl⟩
#align setoid.eq_iff_rel_eq Setoid.eq_iff_rel_eq
-/

/-- Defining `≤` for equivalence relations. -/
instance : LE (Setoid α) :=
  ⟨fun r s => ∀ ⦃x y⦄, r.Rel x y → s.Rel x y⟩

#print Setoid.le_def /-
theorem le_def {r s : Setoid α} : r ≤ s ↔ ∀ {x y}, r.Rel x y → s.Rel x y :=
  Iff.rfl
#align setoid.le_def Setoid.le_def
-/

#print Setoid.refl' /-
@[refl]
theorem refl' (r : Setoid α) (x) : r.Rel x x :=
  r.2.1 x
#align setoid.refl' Setoid.refl'
-/

#print Setoid.symm' /-
@[symm]
theorem symm' (r : Setoid α) : ∀ {x y}, r.Rel x y → r.Rel y x := fun _ _ h => r.2.2.1 h
#align setoid.symm' Setoid.symm'
-/

#print Setoid.trans' /-
@[trans]
theorem trans' (r : Setoid α) : ∀ {x y z}, r.Rel x y → r.Rel y z → r.Rel x z := fun _ _ _ hx =>
  r.2.2.2 hx
#align setoid.trans' Setoid.trans'
-/

#print Setoid.comm' /-
theorem comm' (s : Setoid α) {x y} : s.Rel x y ↔ s.Rel y x :=
  ⟨s.symm', s.symm'⟩
#align setoid.comm' Setoid.comm'
-/

#print Setoid.ker /-
/-- The kernel of a function is an equivalence relation. -/
def ker (f : α → β) : Setoid α :=
  ⟨(· = ·) on f, eq_equivalence.comap f⟩
#align setoid.ker Setoid.ker
-/

#print Setoid.ker_mk_eq /-
/-- The kernel of the quotient map induced by an equivalence relation r equals r. -/
@[simp]
theorem ker_mk_eq (r : Setoid α) : ker (@Quotient.mk'' _ r) = r :=
  ext' fun x y => Quotient.eq
#align setoid.ker_mk_eq Setoid.ker_mk_eq
-/

#print Setoid.ker_apply_mk_out /-
theorem ker_apply_mk_out {f : α → β} (a : α) :
    (f
        haveI := Setoid.ker f
        ⟦a⟧.out) =
      f a :=
  @Quotient.mk_out _ (Setoid.ker f) a
#align setoid.ker_apply_mk_out Setoid.ker_apply_mk_out
-/

#print Setoid.ker_apply_mk_out' /-
theorem ker_apply_mk_out' {f : α → β} (a : α) :
    f (Quotient.mk' a : Quotient <| Setoid.ker f).out' = f a :=
  @Quotient.mk_out' _ (Setoid.ker f) a
#align setoid.ker_apply_mk_out' Setoid.ker_apply_mk_out'
-/

/- warning: setoid.ker_def -> Setoid.ker_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x : α} {y : α}, Iff (Setoid.Rel.{u1} α (Setoid.ker.{u1, u2} α β f) x y) (Eq.{succ u2} β (f x) (f y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {x : α} {y : α}, Iff (Setoid.Rel.{u2} α (Setoid.ker.{u2, u1} α β f) x y) (Eq.{succ u1} β (f x) (f y))
Case conversion may be inaccurate. Consider using '#align setoid.ker_def Setoid.ker_defₓ'. -/
theorem ker_def {f : α → β} {x y : α} : (ker f).Rel x y ↔ f x = f y :=
  Iff.rfl
#align setoid.ker_def Setoid.ker_def

#print Setoid.prod /-
/-- Given types `α`, `β`, the product of two equivalence relations `r` on `α` and `s` on `β`:
    `(x₁, x₂), (y₁, y₂) ∈ α × β` are related by `r.prod s` iff `x₁` is related to `y₁`
    by `r` and `x₂` is related to `y₂` by `s`. -/
protected def prod (r : Setoid α) (s : Setoid β) : Setoid (α × β)
    where
  R x y := r.Rel x.1 y.1 ∧ s.Rel x.2 y.2
  iseqv :=
    ⟨fun x => ⟨r.refl' x.1, s.refl' x.2⟩, fun _ _ h => ⟨r.symm' h.1, s.symm' h.2⟩,
      fun _ _ _ h1 h2 => ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩
#align setoid.prod Setoid.prod
-/

/-- The infimum of two equivalence relations. -/
instance : HasInf (Setoid α) :=
  ⟨fun r s =>
    ⟨fun x y => r.Rel x y ∧ s.Rel x y,
      ⟨fun x => ⟨r.refl' x, s.refl' x⟩, fun _ _ h => ⟨r.symm' h.1, s.symm' h.2⟩, fun _ _ _ h1 h2 =>
        ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩⟩

/- warning: setoid.inf_def -> Setoid.inf_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : Setoid.{succ u1} α} {s : Setoid.{succ u1} α}, Eq.{succ u1} (α -> α -> Prop) (Setoid.Rel.{u1} α (HasInf.inf.{u1} (Setoid.{succ u1} α) (Setoid.hasInf.{u1} α) r s)) (HasInf.inf.{u1} (α -> α -> Prop) (Pi.hasInf.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasInf.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => SemilatticeInf.toHasInf.{0} Prop (Lattice.toSemilatticeInf.{0} Prop (CompleteLattice.toLattice.{0} Prop Prop.completeLattice))))) (Setoid.Rel.{u1} α r) (Setoid.Rel.{u1} α s))
but is expected to have type
  forall {α : Type.{u1}} {r : Setoid.{succ u1} α} {s : Setoid.{succ u1} α}, Eq.{succ u1} (α -> α -> Prop) (Setoid.Rel.{u1} α (HasInf.inf.{u1} (Setoid.{succ u1} α) (Setoid.instHasInfSetoid.{u1} α) r s)) (HasInf.inf.{u1} (α -> α -> Prop) (Pi.instHasInfForAll.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.instHasInfForAll.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => Lattice.toHasInf.{0} Prop (CompleteLattice.toLattice.{0} Prop Prop.completeLattice)))) (Setoid.Rel.{u1} α r) (Setoid.Rel.{u1} α s))
Case conversion may be inaccurate. Consider using '#align setoid.inf_def Setoid.inf_defₓ'. -/
/-- The infimum of 2 equivalence relations r and s is the same relation as the infimum
    of the underlying binary operations. -/
theorem inf_def {r s : Setoid α} : (r ⊓ s).Rel = r.Rel ⊓ s.Rel :=
  rfl
#align setoid.inf_def Setoid.inf_def

/- warning: setoid.inf_iff_and -> Setoid.inf_iff_and is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : Setoid.{succ u1} α} {s : Setoid.{succ u1} α} {x : α} {y : α}, Iff (Setoid.Rel.{u1} α (HasInf.inf.{u1} (Setoid.{succ u1} α) (Setoid.hasInf.{u1} α) r s) x y) (And (Setoid.Rel.{u1} α r x y) (Setoid.Rel.{u1} α s x y))
but is expected to have type
  forall {α : Type.{u1}} {r : Setoid.{succ u1} α} {s : Setoid.{succ u1} α} {x : α} {y : α}, Iff (Setoid.Rel.{u1} α (HasInf.inf.{u1} (Setoid.{succ u1} α) (Setoid.instHasInfSetoid.{u1} α) r s) x y) (And (Setoid.Rel.{u1} α r x y) (Setoid.Rel.{u1} α s x y))
Case conversion may be inaccurate. Consider using '#align setoid.inf_iff_and Setoid.inf_iff_andₓ'. -/
theorem inf_iff_and {r s : Setoid α} {x y} : (r ⊓ s).Rel x y ↔ r.Rel x y ∧ s.Rel x y :=
  Iff.rfl
#align setoid.inf_iff_and Setoid.inf_iff_and

/-- The infimum of a set of equivalence relations. -/
instance : InfSet (Setoid α) :=
  ⟨fun S =>
    ⟨fun x y => ∀ r ∈ S, Rel r x y,
      ⟨fun x r hr => r.refl' x, fun _ _ h r hr => r.symm' <| h r hr, fun _ _ _ h1 h2 r hr =>
        r.trans' (h1 r hr) <| h2 r hr⟩⟩⟩

#print Setoid.infₛ_def /-
/-- The underlying binary operation of the infimum of a set of equivalence relations
    is the infimum of the set's image under the map to the underlying binary operation. -/
theorem infₛ_def {s : Set (Setoid α)} : (infₛ s).Rel = infₛ (Rel '' s) :=
  by
  ext
  simp only [infₛ_image, infᵢ_apply, infᵢ_Prop_eq]
  rfl
#align setoid.Inf_def Setoid.infₛ_def
-/

instance : PartialOrder (Setoid α) where
  le := (· ≤ ·)
  lt r s := r ≤ s ∧ ¬s ≤ r
  le_refl _ _ _ := id
  le_trans _ _ _ hr hs _ _ h := hs <| hr h
  lt_iff_le_not_le _ _ := Iff.rfl
  le_antisymm r s h1 h2 := Setoid.ext' fun x y => ⟨fun h => h1 h, fun h => h2 h⟩

#print Setoid.completeLattice /-
/-- The complete lattice of equivalence relations on a type, with bottom element `=`
    and top element the trivial equivalence relation. -/
instance completeLattice : CompleteLattice (Setoid α) :=
  {
    (completeLatticeOfInf (Setoid α)) fun s =>
      ⟨fun r hr x y h => h _ hr, fun r hr x y h r' hr' =>
        hr hr' h⟩ with
    inf := HasInf.inf
    inf_le_left := fun _ _ _ _ h => h.1
    inf_le_right := fun _ _ _ _ h => h.2
    le_inf := fun _ _ _ h1 h2 _ _ h => ⟨h1 h, h2 h⟩
    top := ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ _ h => h, fun _ _ _ h1 h2 => h1⟩⟩
    le_top := fun _ _ _ _ => trivial
    bot := ⟨(· = ·), ⟨fun _ => rfl, fun _ _ h => h.symm, fun _ _ _ h1 h2 => h1.trans h2⟩⟩
    bot_le := fun r x y h => h ▸ r.2.1 x }
#align setoid.complete_lattice Setoid.completeLattice
-/

/- warning: setoid.top_def -> Setoid.top_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (α -> α -> Prop) (Setoid.Rel.{u1} α (Top.top.{u1} (Setoid.{succ u1} α) (CompleteLattice.toHasTop.{u1} (Setoid.{succ u1} α) (Setoid.completeLattice.{u1} α)))) (Top.top.{u1} (α -> α -> Prop) (Pi.hasTop.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasTop.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toHasTop.{0} Prop Prop.completeLattice))))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (α -> α -> Prop) (Setoid.Rel.{u1} α (Top.top.{u1} (Setoid.{succ u1} α) (CompleteLattice.toTop.{u1} (Setoid.{succ u1} α) (Setoid.completeLattice.{u1} α)))) (Top.top.{u1} (α -> α -> Prop) (Pi.instTopForAll.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.instTopForAll.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toTop.{0} Prop Prop.completeLattice))))
Case conversion may be inaccurate. Consider using '#align setoid.top_def Setoid.top_defₓ'. -/
@[simp]
theorem top_def : (⊤ : Setoid α).Rel = ⊤ :=
  rfl
#align setoid.top_def Setoid.top_def

/- warning: setoid.bot_def -> Setoid.bot_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (α -> α -> Prop) (Setoid.Rel.{u1} α (Bot.bot.{u1} (Setoid.{succ u1} α) (CompleteLattice.toHasBot.{u1} (Setoid.{succ u1} α) (Setoid.completeLattice.{u1} α)))) (Eq.{succ u1} α)
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (α -> α -> Prop) (Setoid.Rel.{u1} α (Bot.bot.{u1} (Setoid.{succ u1} α) (CompleteLattice.toBot.{u1} (Setoid.{succ u1} α) (Setoid.completeLattice.{u1} α)))) (fun (x._@.Mathlib.Data.Setoid.Basic._hyg.1216 : α) (x._@.Mathlib.Data.Setoid.Basic._hyg.1218 : α) => Eq.{succ u1} α x._@.Mathlib.Data.Setoid.Basic._hyg.1216 x._@.Mathlib.Data.Setoid.Basic._hyg.1218)
Case conversion may be inaccurate. Consider using '#align setoid.bot_def Setoid.bot_defₓ'. -/
@[simp]
theorem bot_def : (⊥ : Setoid α).Rel = (· = ·) :=
  rfl
#align setoid.bot_def Setoid.bot_def

/- warning: setoid.eq_top_iff -> Setoid.eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Setoid.{succ u1} α}, Iff (Eq.{succ u1} (Setoid.{succ u1} α) s (Top.top.{u1} (Setoid.{succ u1} α) (CompleteLattice.toHasTop.{u1} (Setoid.{succ u1} α) (Setoid.completeLattice.{u1} α)))) (forall (x : α) (y : α), Setoid.Rel.{u1} α s x y)
but is expected to have type
  forall {α : Type.{u1}} {s : Setoid.{succ u1} α}, Iff (Eq.{succ u1} (Setoid.{succ u1} α) s (Top.top.{u1} (Setoid.{succ u1} α) (CompleteLattice.toTop.{u1} (Setoid.{succ u1} α) (Setoid.completeLattice.{u1} α)))) (forall (x : α) (y : α), Setoid.Rel.{u1} α s x y)
Case conversion may be inaccurate. Consider using '#align setoid.eq_top_iff Setoid.eq_top_iffₓ'. -/
theorem eq_top_iff {s : Setoid α} : s = (⊤ : Setoid α) ↔ ∀ x y : α, s.Rel x y := by
  simp [eq_top_iff, Setoid.le_def, Setoid.top_def, Pi.top_apply]
#align setoid.eq_top_iff Setoid.eq_top_iff

#print Setoid.eqvGen_eq /-
/-- The inductively defined equivalence closure of a binary relation r is the infimum
    of the set of all equivalence relations containing r. -/
theorem eqvGen_eq (r : α → α → Prop) :
    EqvGen.Setoid r = infₛ { s : Setoid α | ∀ ⦃x y⦄, r x y → s.Rel x y } :=
  le_antisymm
    (fun _ _ H =>
      EqvGen.ndrec (fun _ _ h _ hs => hs h) (refl' _) (fun _ _ _ => symm' _)
        (fun _ _ _ _ _ => trans' _) H)
    (infₛ_le fun _ _ h => EqvGen.rel _ _ h)
#align setoid.eqv_gen_eq Setoid.eqvGen_eq
-/

#print Setoid.sup_eq_eqvGen /-
/-- The supremum of two equivalence relations r and s is the equivalence closure of the binary
    relation `x is related to y by r or s`. -/
theorem sup_eq_eqvGen (r s : Setoid α) : r ⊔ s = EqvGen.Setoid fun x y => r.Rel x y ∨ s.Rel x y :=
  by
  rw [eqv_gen_eq]
  apply congr_arg Inf
  simp only [le_def, or_imp, ← forall_and]
#align setoid.sup_eq_eqv_gen Setoid.sup_eq_eqvGen
-/

#print Setoid.sup_def /-
/-- The supremum of 2 equivalence relations r and s is the equivalence closure of the
    supremum of the underlying binary operations. -/
theorem sup_def {r s : Setoid α} : r ⊔ s = EqvGen.Setoid (r.Rel ⊔ s.Rel) := by
  rw [sup_eq_eqv_gen] <;> rfl
#align setoid.sup_def Setoid.sup_def
-/

/- warning: setoid.Sup_eq_eqv_gen -> Setoid.supₛ_eq_eqvGen is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Set.{u1} (Setoid.{succ u1} α)), Eq.{succ u1} (Setoid.{succ u1} α) (SupSet.supₛ.{u1} (Setoid.{succ u1} α) (CompleteSemilatticeSup.toHasSup.{u1} (Setoid.{succ u1} α) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Setoid.{succ u1} α) (Setoid.completeLattice.{u1} α))) S) (EqvGen.Setoid.{u1} α (fun (x : α) (y : α) => Exists.{succ u1} (Setoid.{succ u1} α) (fun (r : Setoid.{succ u1} α) => And (Membership.Mem.{u1, u1} (Setoid.{succ u1} α) (Set.{u1} (Setoid.{succ u1} α)) (Set.hasMem.{u1} (Setoid.{succ u1} α)) r S) (Setoid.Rel.{u1} α r x y))))
but is expected to have type
  forall {α : Type.{u1}} (S : Set.{u1} (Setoid.{succ u1} α)), Eq.{succ u1} (Setoid.{succ u1} α) (SupSet.supₛ.{u1} (Setoid.{succ u1} α) (CompleteLattice.toSupSet.{u1} (Setoid.{succ u1} α) (Setoid.completeLattice.{u1} α)) S) (EqvGen.Setoid.{u1} α (fun (x : α) (y : α) => Exists.{succ u1} (Setoid.{succ u1} α) (fun (r : Setoid.{succ u1} α) => And (Membership.mem.{u1, u1} (Setoid.{succ u1} α) (Set.{u1} (Setoid.{succ u1} α)) (Set.instMembershipSet.{u1} (Setoid.{succ u1} α)) r S) (Setoid.Rel.{u1} α r x y))))
Case conversion may be inaccurate. Consider using '#align setoid.Sup_eq_eqv_gen Setoid.supₛ_eq_eqvGenₓ'. -/
/-- The supremum of a set S of equivalence relations is the equivalence closure of the binary
    relation `there exists r ∈ S relating x and y`. -/
theorem supₛ_eq_eqvGen (S : Set (Setoid α)) :
    supₛ S = EqvGen.Setoid fun x y => ∃ r : Setoid α, r ∈ S ∧ r.Rel x y :=
  by
  rw [eqv_gen_eq]
  apply congr_arg Inf
  simp only [upperBounds, le_def, and_imp, exists_imp]
  ext
  exact ⟨fun H x y r hr => H hr, fun H r hr x y => H r hr⟩
#align setoid.Sup_eq_eqv_gen Setoid.supₛ_eq_eqvGen

/- warning: setoid.Sup_def -> Setoid.supₛ_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} (Setoid.{succ u1} α)}, Eq.{succ u1} (Setoid.{succ u1} α) (SupSet.supₛ.{u1} (Setoid.{succ u1} α) (CompleteSemilatticeSup.toHasSup.{u1} (Setoid.{succ u1} α) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Setoid.{succ u1} α) (Setoid.completeLattice.{u1} α))) s) (EqvGen.Setoid.{u1} α (SupSet.supₛ.{u1} (α -> α -> Prop) (Pi.supSet.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.supSet.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteSemilatticeSup.toHasSup.{0} Prop (CompleteLattice.toCompleteSemilatticeSup.{0} Prop Prop.completeLattice)))) (Set.image.{u1, u1} (Setoid.{succ u1} α) (α -> α -> Prop) (Setoid.Rel.{u1} α) s)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} (Setoid.{succ u1} α)}, Eq.{succ u1} (Setoid.{succ u1} α) (SupSet.supₛ.{u1} (Setoid.{succ u1} α) (CompleteLattice.toSupSet.{u1} (Setoid.{succ u1} α) (Setoid.completeLattice.{u1} α)) s) (EqvGen.Setoid.{u1} α (SupSet.supₛ.{u1} (α -> α -> Prop) (Pi.supSet.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.supSet.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toSupSet.{0} Prop Prop.completeLattice))) (Set.image.{u1, u1} (Setoid.{succ u1} α) (α -> α -> Prop) (Setoid.Rel.{u1} α) s)))
Case conversion may be inaccurate. Consider using '#align setoid.Sup_def Setoid.supₛ_defₓ'. -/
/-- The supremum of a set of equivalence relations is the equivalence closure of the
    supremum of the set's image under the map to the underlying binary operation. -/
theorem supₛ_def {s : Set (Setoid α)} : supₛ s = EqvGen.Setoid (supₛ (Rel '' s)) :=
  by
  rw [Sup_eq_eqv_gen, supₛ_image]
  congr with (x y)
  simp only [supᵢ_apply, supᵢ_Prop_eq, exists_prop]
#align setoid.Sup_def Setoid.supₛ_def

#print Setoid.eqvGen_of_setoid /-
/-- The equivalence closure of an equivalence relation r is r. -/
@[simp]
theorem eqvGen_of_setoid (r : Setoid α) : EqvGen.Setoid r.R = r :=
  le_antisymm (by rw [eqv_gen_eq] <;> exact infₛ_le fun _ _ => id) EqvGen.rel
#align setoid.eqv_gen_of_setoid Setoid.eqvGen_of_setoid
-/

#print Setoid.eqvGen_idem /-
/-- Equivalence closure is idempotent. -/
@[simp]
theorem eqvGen_idem (r : α → α → Prop) : EqvGen.Setoid (EqvGen.Setoid r).Rel = EqvGen.Setoid r :=
  eqvGen_of_setoid _
#align setoid.eqv_gen_idem Setoid.eqvGen_idem
-/

#print Setoid.eqvGen_le /-
/-- The equivalence closure of a binary relation r is contained in any equivalence
    relation containing r. -/
theorem eqvGen_le {r : α → α → Prop} {s : Setoid α} (h : ∀ x y, r x y → s.Rel x y) :
    EqvGen.Setoid r ≤ s := by rw [eqv_gen_eq] <;> exact infₛ_le h
#align setoid.eqv_gen_le Setoid.eqvGen_le
-/

#print Setoid.eqvGen_mono /-
/-- Equivalence closure of binary relations is monotone. -/
theorem eqvGen_mono {r s : α → α → Prop} (h : ∀ x y, r x y → s x y) :
    EqvGen.Setoid r ≤ EqvGen.Setoid s :=
  eqv_gen_le fun _ _ hr => EqvGen.rel _ _ <| h _ _ hr
#align setoid.eqv_gen_mono Setoid.eqvGen_mono
-/

/- warning: setoid.gi -> Setoid.gi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, GaloisInsertion.{u1, u1} (α -> α -> Prop) (Setoid.{succ u1} α) (Pi.preorder.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.preorder.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => PartialOrder.toPreorder.{0} Prop Prop.partialOrder))) (PartialOrder.toPreorder.{u1} (Setoid.{succ u1} α) (Setoid.partialOrder.{u1} α)) (EqvGen.Setoid.{u1} α) (Setoid.Rel.{u1} α)
but is expected to have type
  forall {α : Type.{u1}}, GaloisInsertion.{u1, u1} (α -> α -> Prop) (Setoid.{succ u1} α) (Pi.preorder.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.preorder.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => PartialOrder.toPreorder.{0} Prop Prop.partialOrder))) (PartialOrder.toPreorder.{u1} (Setoid.{succ u1} α) (Setoid.instPartialOrderSetoid.{u1} α)) (EqvGen.Setoid.{u1} α) (Setoid.Rel.{u1} α)
Case conversion may be inaccurate. Consider using '#align setoid.gi Setoid.giₓ'. -/
/-- There is a Galois insertion of equivalence relations on α into binary relations
    on α, with equivalence closure the lower adjoint. -/
def gi : @GaloisInsertion (α → α → Prop) (Setoid α) _ _ EqvGen.Setoid Rel
    where
  choice r h := EqvGen.Setoid r
  gc r s := ⟨fun H _ _ h => H <| EqvGen.rel _ _ h, fun H => eqvGen_of_setoid s ▸ eqvGen_mono H⟩
  le_l_u x := (eqvGen_of_setoid x).symm ▸ le_refl x
  choice_eq _ _ := rfl
#align setoid.gi Setoid.gi

open Function

/- warning: setoid.injective_iff_ker_bot -> Setoid.injective_iff_ker_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Iff (Function.Injective.{succ u1, succ u2} α β f) (Eq.{succ u1} (Setoid.{succ u1} α) (Setoid.ker.{u1, u2} α β f) (Bot.bot.{u1} (Setoid.{succ u1} α) (CompleteLattice.toHasBot.{u1} (Setoid.{succ u1} α) (Setoid.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Iff (Function.Injective.{succ u2, succ u1} α β f) (Eq.{succ u2} (Setoid.{succ u2} α) (Setoid.ker.{u2, u1} α β f) (Bot.bot.{u2} (Setoid.{succ u2} α) (CompleteLattice.toBot.{u2} (Setoid.{succ u2} α) (Setoid.completeLattice.{u2} α))))
Case conversion may be inaccurate. Consider using '#align setoid.injective_iff_ker_bot Setoid.injective_iff_ker_botₓ'. -/
/-- A function from α to β is injective iff its kernel is the bottom element of the complete lattice
    of equivalence relations on α. -/
theorem injective_iff_ker_bot (f : α → β) : Injective f ↔ ker f = ⊥ :=
  (@eq_bot_iff (Setoid α) _ _ (ker f)).symm
#align setoid.injective_iff_ker_bot Setoid.injective_iff_ker_bot

/- warning: setoid.ker_iff_mem_preimage -> Setoid.ker_iff_mem_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {x : α} {y : α}, Iff (Setoid.Rel.{u1} α (Setoid.ker.{u1, u2} α β f) x y) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.preimage.{u1, u2} α β f (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) (f y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {x : α} {y : α}, Iff (Setoid.Rel.{u2} α (Setoid.ker.{u2, u1} α β f) x y) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.preimage.{u2, u1} α β f (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) (f y))))
Case conversion may be inaccurate. Consider using '#align setoid.ker_iff_mem_preimage Setoid.ker_iff_mem_preimageₓ'. -/
/-- The elements related to x ∈ α by the kernel of f are those in the preimage of f(x) under f. -/
theorem ker_iff_mem_preimage {f : α → β} {x y} : (ker f).Rel x y ↔ x ∈ f ⁻¹' {f y} :=
  Iff.rfl
#align setoid.ker_iff_mem_preimage Setoid.ker_iff_mem_preimage

#print Setoid.liftEquiv /-
/-- Equivalence between functions `α → β` such that `r x y → f x = f y` and functions
`quotient r → β`. -/
def liftEquiv (r : Setoid α) : { f : α → β // r ≤ ker f } ≃ (Quotient r → β)
    where
  toFun f := Quotient.lift (f : α → β) f.2
  invFun f := ⟨f ∘ Quotient.mk'', fun x y h => by simp [ker_def, Quotient.sound h]⟩
  left_inv := fun ⟨f, hf⟩ => Subtype.eq <| funext fun x => rfl
  right_inv f := funext fun x => (Quotient.inductionOn' x) fun x => rfl
#align setoid.lift_equiv Setoid.liftEquiv
-/

/- warning: setoid.lift_unique -> Setoid.lift_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : Setoid.{succ u1} α} {f : α -> β} (H : LE.le.{u1} (Setoid.{succ u1} α) (Setoid.hasLe.{u1} α) r (Setoid.ker.{u1, u2} α β f)) (g : (Quotient.{succ u1} α r) -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f (Function.comp.{succ u1, succ u1, succ u2} α (Quotient.{succ u1} α r) β g (Quotient.mk''.{succ u1} α r))) -> (Eq.{max (succ u1) (succ u2)} ((Quotient.{succ u1} α r) -> β) (Quotient.lift.{succ u1, succ u2} α β r f H) g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : Setoid.{succ u2} α} {f : α -> β} (H : LE.le.{u2} (Setoid.{succ u2} α) (Setoid.instLESetoid.{u2} α) r (Setoid.ker.{u2, u1} α β f)) (g : (Quotient.{succ u2} α r) -> β), (Eq.{max (succ u2) (succ u1)} (α -> β) f (Function.comp.{succ u2, succ u2, succ u1} α (Quotient.{succ u2} α r) β g (Quotient.mk''.{succ u2} α r))) -> (Eq.{max (succ u2) (succ u1)} ((Quotient.{succ u2} α r) -> β) (Quotient.lift.{succ u2, succ u1} α β r f H) g)
Case conversion may be inaccurate. Consider using '#align setoid.lift_unique Setoid.lift_uniqueₓ'. -/
/-- The uniqueness part of the universal property for quotients of an arbitrary type. -/
theorem lift_unique {r : Setoid α} {f : α → β} (H : r ≤ ker f) (g : Quotient r → β)
    (Hg : f = g ∘ Quotient.mk'') : Quotient.lift f H = g :=
  by
  ext ⟨x⟩
  erw [Quotient.lift_mk f H, Hg]
  rfl
#align setoid.lift_unique Setoid.lift_unique

/- warning: setoid.ker_lift_injective -> Setoid.ker_lift_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Function.Injective.{succ u1, succ u2} (Quotient.{succ u1} α (Setoid.ker.{u1, u2} α β f)) β (Quotient.lift.{succ u1, succ u2} α β (Setoid.ker.{u1, u2} α β f) f (fun (_x : α) (_x_1 : α) (h : HasEquivₓ.Equiv.{succ u1} α (setoidHasEquiv.{succ u1} α (Setoid.ker.{u1, u2} α β f)) _x _x_1) => h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Function.Injective.{succ u2, succ u1} (Quotient.{succ u2} α (Setoid.ker.{u2, u1} α β f)) β (Quotient.lift.{succ u2, succ u1} α β (Setoid.ker.{u2, u1} α β f) f (fun (_x : α) (_x_1 : α) (h : HasEquiv.Equiv.{succ u2, 0} α (instHasEquiv.{succ u2} α (Setoid.ker.{u2, u1} α β f)) _x _x_1) => h))
Case conversion may be inaccurate. Consider using '#align setoid.ker_lift_injective Setoid.ker_lift_injectiveₓ'. -/
/-- Given a map f from α to β, the natural map from the quotient of α by the kernel of f is
    injective. -/
theorem ker_lift_injective (f : α → β) : Injective (@Quotient.lift _ _ (ker f) f fun _ _ h => h) :=
  fun x y => (Quotient.inductionOn₂' x y) fun a b h => Quotient.sound' h
#align setoid.ker_lift_injective Setoid.ker_lift_injective

/- warning: setoid.ker_eq_lift_of_injective -> Setoid.ker_eq_lift_of_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : Setoid.{succ u1} α} (f : α -> β) (H : forall (x : α) (y : α), (Setoid.Rel.{u1} α r x y) -> (Eq.{succ u2} β (f x) (f y))), (Function.Injective.{succ u1, succ u2} (Quotient.{succ u1} α r) β (Quotient.lift.{succ u1, succ u2} α β r f H)) -> (Eq.{succ u1} (Setoid.{succ u1} α) (Setoid.ker.{u1, u2} α β f) r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : Setoid.{succ u2} α} (f : α -> β) (H : forall (x : α) (y : α), (Setoid.Rel.{u2} α r x y) -> (Eq.{succ u1} β (f x) (f y))), (Function.Injective.{succ u2, succ u1} (Quotient.{succ u2} α r) β (Quotient.lift.{succ u2, succ u1} α β r f H)) -> (Eq.{succ u2} (Setoid.{succ u2} α) (Setoid.ker.{u2, u1} α β f) r)
Case conversion may be inaccurate. Consider using '#align setoid.ker_eq_lift_of_injective Setoid.ker_eq_lift_of_injectiveₓ'. -/
/-- Given a map f from α to β, the kernel of f is the unique equivalence relation on α whose
    induced map from the quotient of α to β is injective. -/
theorem ker_eq_lift_of_injective {r : Setoid α} (f : α → β) (H : ∀ x y, r.Rel x y → f x = f y)
    (h : Injective (Quotient.lift f H)) : ker f = r :=
  le_antisymm
    (fun x y hk =>
      Quotient.exact <| h <| show Quotient.lift f H ⟦x⟧ = Quotient.lift f H ⟦y⟧ from hk)
    H
#align setoid.ker_eq_lift_of_injective Setoid.ker_eq_lift_of_injective

variable (r : Setoid α) (f : α → β)

#print Setoid.quotientKerEquivRange /-
/-- The first isomorphism theorem for sets: the quotient of α by the kernel of a function f
    bijects with f's image. -/
noncomputable def quotientKerEquivRange : Quotient (ker f) ≃ Set.range f :=
  Equiv.ofBijective
    ((@Quotient.lift _ (Set.range f) (ker f) fun x => ⟨f x, Set.mem_range_self x⟩) fun _ _ h =>
      Subtype.ext_val h)
    ⟨fun x y h => ker_lift_injective f <| by rcases x with ⟨⟩ <;> rcases y with ⟨⟩ <;> injections,
      fun ⟨w, z, hz⟩ =>
      ⟨@Quotient.mk'' _ (ker f) z, by rw [Quotient.lift_mk] <;> exact Subtype.ext_iff_val.2 hz⟩⟩
#align setoid.quotient_ker_equiv_range Setoid.quotientKerEquivRange
-/

#print Setoid.quotientKerEquivOfRightInverse /-
/-- If `f` has a computable right-inverse, then the quotient by its kernel is equivalent to its
domain. -/
@[simps]
def quotientKerEquivOfRightInverse (g : β → α) (hf : Function.RightInverse g f) :
    Quotient (ker f) ≃ β
    where
  toFun a := (Quotient.liftOn' a f) fun _ _ => id
  invFun b := Quotient.mk' (g b)
  left_inv a := (Quotient.inductionOn' a) fun a => Quotient.sound' <| hf (f a)
  right_inv := hf
#align setoid.quotient_ker_equiv_of_right_inverse Setoid.quotientKerEquivOfRightInverse
-/

#print Setoid.quotientKerEquivOfSurjective /-
/-- The quotient of α by the kernel of a surjective function f bijects with f's codomain.

If a specific right-inverse of `f` is known, `setoid.quotient_ker_equiv_of_right_inverse` can be
definitionally more useful. -/
noncomputable def quotientKerEquivOfSurjective (hf : Surjective f) : Quotient (ker f) ≃ β :=
  quotientKerEquivOfRightInverse _ (Function.surjInv hf) (right_inverse_surj_inv hf)
#align setoid.quotient_ker_equiv_of_surjective Setoid.quotientKerEquivOfSurjective
-/

variable {r f}

#print Setoid.map /-
/-- Given a function `f : α → β` and equivalence relation `r` on `α`, the equivalence
    closure of the relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are
    related to the elements of `f⁻¹(y)` by `r`.' -/
def map (r : Setoid α) (f : α → β) : Setoid β :=
  EqvGen.Setoid fun x y => ∃ a b, f a = x ∧ f b = y ∧ r.Rel a b
#align setoid.map Setoid.map
-/

#print Setoid.mapOfSurjective /-
/-- Given a surjective function f whose kernel is contained in an equivalence relation r, the
    equivalence relation on f's codomain defined by x ≈ y ↔ the elements of f⁻¹(x) are related to
    the elements of f⁻¹(y) by r. -/
def mapOfSurjective (r) (f : α → β) (h : ker f ≤ r) (hf : Surjective f) : Setoid β :=
  ⟨fun x y => ∃ a b, f a = x ∧ f b = y ∧ r.Rel a b,
    ⟨fun x =>
      let ⟨y, hy⟩ := hf x
      ⟨y, y, hy, hy, r.refl' y⟩,
      fun _ _ ⟨x, y, hx, hy, h⟩ => ⟨y, x, hy, hx, r.symm' h⟩,
      fun _ _ _ ⟨x, y, hx, hy, h₁⟩ ⟨y', z, hy', hz, h₂⟩ =>
      ⟨x, z, hx, hz, r.trans' h₁ <| r.trans' (h <| by rwa [← hy'] at hy) h₂⟩⟩⟩
#align setoid.map_of_surjective Setoid.mapOfSurjective
-/

/- warning: setoid.map_of_surjective_eq_map -> Setoid.mapOfSurjective_eq_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : Setoid.{succ u1} α} {f : α -> β} (h : LE.le.{u1} (Setoid.{succ u1} α) (Setoid.hasLe.{u1} α) (Setoid.ker.{u1, u2} α β f) r) (hf : Function.Surjective.{succ u1, succ u2} α β f), Eq.{succ u2} (Setoid.{succ u2} β) (Setoid.map.{u1, u2} α β r f) (Setoid.mapOfSurjective.{u1, u2} α β r f h hf)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : Setoid.{succ u2} α} {f : α -> β} (h : LE.le.{u2} (Setoid.{succ u2} α) (Setoid.instLESetoid.{u2} α) (Setoid.ker.{u2, u1} α β f) r) (hf : Function.Surjective.{succ u2, succ u1} α β f), Eq.{succ u1} (Setoid.{succ u1} β) (Setoid.map.{u2, u1} α β r f) (Setoid.mapOfSurjective.{u2, u1} α β r f h hf)
Case conversion may be inaccurate. Consider using '#align setoid.map_of_surjective_eq_map Setoid.mapOfSurjective_eq_mapₓ'. -/
/-- A special case of the equivalence closure of an equivalence relation r equalling r. -/
theorem mapOfSurjective_eq_map (h : ker f ≤ r) (hf : Surjective f) :
    map r f = mapOfSurjective r f h hf := by
  rw [← eqv_gen_of_setoid (map_of_surjective r f h hf)] <;> rfl
#align setoid.map_of_surjective_eq_map Setoid.mapOfSurjective_eq_map

#print Setoid.comap /-
/-- Given a function `f : α → β`, an equivalence relation `r` on `β` induces an equivalence
relation on `α` defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `r`'.

See note [reducible non-instances]. -/
@[reducible]
def comap (f : α → β) (r : Setoid β) : Setoid α :=
  ⟨r.Rel on f, r.iseqv.comap _⟩
#align setoid.comap Setoid.comap
-/

#print Setoid.comap_rel /-
theorem comap_rel (f : α → β) (r : Setoid β) (x y : α) : (comap f r).Rel x y ↔ r.Rel (f x) (f y) :=
  Iff.rfl
#align setoid.comap_rel Setoid.comap_rel
-/

#print Setoid.comap_eq /-
/-- Given a map `f : N → M` and an equivalence relation `r` on `β`, the equivalence relation
    induced on `α` by `f` equals the kernel of `r`'s quotient map composed with `f`. -/
theorem comap_eq {f : α → β} {r : Setoid β} : comap f r = ker (@Quotient.mk'' _ r ∘ f) :=
  ext fun x y => show _ ↔ ⟦_⟧ = ⟦_⟧ by rw [Quotient.eq] <;> rfl
#align setoid.comap_eq Setoid.comap_eq
-/

#print Setoid.comapQuotientEquiv /-
/-- The second isomorphism theorem for sets. -/
noncomputable def comapQuotientEquiv (f : α → β) (r : Setoid β) :
    Quotient (comap f r) ≃ Set.range (@Quotient.mk'' _ r ∘ f) :=
  (Quotient.congrRight <| ext_iff.1 comap_eq).trans <| quotient_ker_equiv_range <| Quotient.mk'' ∘ f
#align setoid.comap_quotient_equiv Setoid.comapQuotientEquiv
-/

variable (r f)

#print Setoid.quotientQuotientEquivQuotient /-
/-- The third isomorphism theorem for sets. -/
def quotientQuotientEquivQuotient (s : Setoid α) (h : r ≤ s) :
    Quotient (ker (Quot.mapRight h)) ≃ Quotient s
    where
  toFun x :=
    (Quotient.liftOn' x fun w =>
        (Quotient.liftOn' w (@Quotient.mk'' _ s)) fun x y H => Quotient.sound <| h H)
      fun x y =>
      (Quotient.inductionOn₂' x y) fun w z H => show @Quot.mk _ _ _ = @Quot.mk _ _ _ from H
  invFun x :=
    (Quotient.liftOn' x fun w => @Quotient.mk'' _ (ker <| Quot.mapRight h) <| @Quotient.mk'' _ r w)
      fun x y H => Quotient.sound' <| show @Quot.mk _ _ _ = @Quot.mk _ _ _ from Quotient.sound H
  left_inv x :=
    (Quotient.inductionOn' x) fun y => (Quotient.inductionOn' y) fun w => by show ⟦_⟧ = _ <;> rfl
  right_inv x := (Quotient.inductionOn' x) fun y => by show ⟦_⟧ = _ <;> rfl
#align setoid.quotient_quotient_equiv_quotient Setoid.quotientQuotientEquivQuotient
-/

variable {r f}

open Quotient

#print Setoid.correspondence /-
/-- Given an equivalence relation `r` on `α`, the order-preserving bijection between the set of
equivalence relations containing `r` and the equivalence relations on the quotient of `α` by `r`. -/
def correspondence (r : Setoid α) : { s // r ≤ s } ≃o Setoid (Quotient r)
    where
  toFun s := mapOfSurjective s.1 Quotient.mk'' ((ker_mk_eq r).symm ▸ s.2) exists_rep
  invFun s := ⟨comap Quotient.mk' s, fun x y h => by rw [comap_rel, eq_rel.2 h]⟩
  left_inv s :=
    Subtype.ext_iff_val.2 <|
      ext' fun _ _ =>
        ⟨fun h =>
          let ⟨a, b, hx, hy, H⟩ := h
          s.1.trans' (s.1.symm' <| s.2 <| eq_rel.1 hx) <| s.1.trans' H <| s.2 <| eq_rel.1 hy,
          fun h => ⟨_, _, rfl, rfl, h⟩⟩
  right_inv s :=
    let Hm : ker Quotient.mk' ≤ comap Quotient.mk' s := fun x y h => by
      rw [comap_rel, (@eq_rel _ r x y).2 (ker_mk_eq r ▸ h)]
    ext' fun x y =>
      ⟨fun h =>
        let ⟨a, b, hx, hy, H⟩ := h
        hx ▸ hy ▸ H,
        (Quotient.induction_on₂ x y) fun w z h => ⟨w, z, rfl, rfl, h⟩⟩
  map_rel_iff' s t :=
    ⟨fun h x y hs =>
      let ⟨a, b, hx, hy, ht⟩ := h ⟨x, y, rfl, rfl, hs⟩
      t.1.trans' (t.1.symm' <| t.2 <| eq_rel.1 hx) <| t.1.trans' ht <| t.2 <| eq_rel.1 hy,
      fun h x y hs =>
      let ⟨a, b, hx, hy, Hs⟩ := hs
      ⟨a, b, hx, hy, h Hs⟩⟩
#align setoid.correspondence Setoid.correspondence
-/

end Setoid

/- warning: quotient.subsingleton_iff -> Quotient.subsingleton_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Setoid.{succ u1} α}, Iff (Subsingleton.{succ u1} (Quotient.{succ u1} α s)) (Eq.{succ u1} (Setoid.{succ u1} α) s (Top.top.{u1} (Setoid.{succ u1} α) (CompleteLattice.toHasTop.{u1} (Setoid.{succ u1} α) (Setoid.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {s : Setoid.{succ u1} α}, Iff (Subsingleton.{succ u1} (Quotient.{succ u1} α s)) (Eq.{succ u1} (Setoid.{succ u1} α) s (Top.top.{u1} (Setoid.{succ u1} α) (CompleteLattice.toTop.{u1} (Setoid.{succ u1} α) (Setoid.completeLattice.{u1} α))))
Case conversion may be inaccurate. Consider using '#align quotient.subsingleton_iff Quotient.subsingleton_iffₓ'. -/
@[simp]
theorem Quotient.subsingleton_iff {s : Setoid α} : Subsingleton (Quotient s) ↔ s = ⊤ :=
  by
  simp only [subsingleton_iff, eq_top_iff, Setoid.le_def, Setoid.top_def, Pi.top_apply,
    forall_const]
  refine' (surjective_quotient_mk _).forall.trans (forall_congr' fun a => _)
  refine' (surjective_quotient_mk _).forall.trans (forall_congr' fun b => _)
  exact Quotient.eq'
#align quotient.subsingleton_iff Quotient.subsingleton_iff

/- warning: quot.subsingleton_iff -> Quot.subsingleton_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (r : α -> α -> Prop), Iff (Subsingleton.{succ u1} (Quot.{succ u1} α r)) (Eq.{succ u1} (α -> α -> Prop) (EqvGen.{u1} α r) (Top.top.{u1} (α -> α -> Prop) (Pi.hasTop.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasTop.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toHasTop.{0} Prop Prop.completeLattice)))))
but is expected to have type
  forall {α : Type.{u1}} (r : α -> α -> Prop), Iff (Subsingleton.{succ u1} (Quot.{succ u1} α r)) (Eq.{succ u1} (α -> α -> Prop) (EqvGen.{u1} α r) (Top.top.{u1} (α -> α -> Prop) (Pi.instTopForAll.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.instTopForAll.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toTop.{0} Prop Prop.completeLattice)))))
Case conversion may be inaccurate. Consider using '#align quot.subsingleton_iff Quot.subsingleton_iffₓ'. -/
theorem Quot.subsingleton_iff (r : α → α → Prop) : Subsingleton (Quot r) ↔ EqvGen r = ⊤ :=
  by
  simp only [subsingleton_iff, _root_.eq_top_iff, Pi.le_def, Pi.top_apply, forall_const]
  refine' (surjective_quot_mk _).forall.trans (forall_congr' fun a => _)
  refine' (surjective_quot_mk _).forall.trans (forall_congr' fun b => _)
  rw [Quot.eq]
  simp only [forall_const, le_Prop_eq]
#align quot.subsingleton_iff Quot.subsingleton_iff

