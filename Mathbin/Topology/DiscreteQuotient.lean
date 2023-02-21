/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Adam Topaz

! This file was ported from Lean 3 source module topology.discrete_quotient
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Separation
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.LocallyConstant.Basic

/-!

# Discrete quotients of a topological space.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the type of discrete quotients of a topological space,
denoted `discrete_quotient X`. To avoid quantifying over types, we model such
quotients as setoids whose equivalence classes are clopen.

## Definitions
1. `discrete_quotient X` is the type of discrete quotients of `X`.
  It is endowed with a coercion to `Type`, which is defined as the
  quotient associated to the setoid in question, and each such quotient
  is endowed with the discrete topology.
2. Given `S : discrete_quotient X`, the projection `X → S` is denoted
  `S.proj`.
3. When `X` is compact and `S : discrete_quotient X`, the space `S` is
  endowed with a `fintype` instance.

## Order structure

The type `discrete_quotient X` is endowed with an instance of a `semilattice_inf` with `order_top`.
The partial ordering `A ≤ B` mathematically means that `B.proj` factors through `A.proj`.
The top element `⊤` is the trivial quotient, meaning that every element of `X` is collapsed
to a point. Given `h : A ≤ B`, the map `A → B` is `discrete_quotient.of_le h`.

Whenever `X` is a locally connected space, the type `discrete_quotient X` is also endowed with an
instance of a `order_bot`, where the bot element `⊥` is given by the `connectedComponentSetoid`,
i.e., `x ~ y` means that `x` and `y` belong to the same connected component. In particular, if `X`
is a discrete topological space, then `x ~ y` is equivalent (propositionally, not definitionally) to
`x = y`.

Given `f : C(X, Y)`, we define a predicate `discrete_quotient.le_comap f A B` for `A :
discrete_quotient X` and `B : discrete_quotient Y`, asserting that `f` descends to `A → B`.  If
`cond : discrete_quotient.le_comap h A B`, the function `A → B` is obtained by
`discrete_quotient.map f cond`.

## Theorems

The two main results proved in this file are:

1. `discrete_quotient.eq_of_forall_proj_eq` which states that when `X` is compact, T₂, and totally
  disconnected, any two elements of `X` are equal if their projections in `Q` agree for all
  `Q : discrete_quotient X`.

2. `discrete_quotient.exists_of_compat` which states that when `X` is compact, then any
  system of elements of `Q` as `Q : discrete_quotient X` varies, which is compatible with
  respect to `discrete_quotient.of_le`, must arise from some element of `X`.

## Remarks
The constructions in this file will be used to show that any profinite space is a limit
of finite discrete spaces.
-/


open Set Function

variable {α X Y Z : Type _} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

#print DiscreteQuotient /-
/-- The type of discrete quotients of a topological space. -/
@[ext]
structure DiscreteQuotient (X : Type _) [TopologicalSpace X] extends Setoid X where
  isOpen_setOf_rel : ∀ x, IsOpen (setOf (to_setoid.Rel x))
#align discrete_quotient DiscreteQuotient
-/

namespace DiscreteQuotient

variable (S : DiscreteQuotient X)

#print DiscreteQuotient.ofClopen /-
/-- Construct a discrete quotient from a clopen set. -/
def ofClopen {A : Set X} (h : IsClopen A) : DiscreteQuotient X
    where
  toSetoid :=
    ⟨fun x y => x ∈ A ↔ y ∈ A, fun _ => Iff.rfl, fun _ _ => Iff.symm, fun _ _ _ => Iff.trans⟩
  isOpen_setOf_rel x := by by_cases hx : x ∈ A <;> simp [Setoid.Rel, hx, h.1, h.2, ← compl_set_of]
#align discrete_quotient.of_clopen DiscreteQuotient.ofClopen
-/

#print DiscreteQuotient.refl /-
theorem refl : ∀ x, S.Rel x x :=
  S.refl'
#align discrete_quotient.refl DiscreteQuotient.refl
-/

#print DiscreteQuotient.symm /-
theorem symm {x y : X} : S.Rel x y → S.Rel y x :=
  S.symm'
#align discrete_quotient.symm DiscreteQuotient.symm
-/

#print DiscreteQuotient.trans /-
theorem trans {x y z} : S.Rel x y → S.Rel y z → S.Rel x z :=
  S.trans'
#align discrete_quotient.trans DiscreteQuotient.trans
-/

/-- The setoid whose quotient yields the discrete quotient. -/
add_decl_doc to_setoid

instance : CoeSort (DiscreteQuotient X) (Type _) :=
  ⟨fun S => Quotient S.toSetoid⟩

instance : TopologicalSpace S :=
  Quotient.topologicalSpace

#print DiscreteQuotient.proj /-
/-- The projection from `X` to the given discrete quotient. -/
def proj : X → S :=
  Quotient.mk''
#align discrete_quotient.proj DiscreteQuotient.proj
-/

#print DiscreteQuotient.fiber_eq /-
theorem fiber_eq (x : X) : S.proj ⁻¹' {S.proj x} = setOf (S.Rel x) :=
  Set.ext fun y => eq_comm.trans Quotient.eq''
#align discrete_quotient.fiber_eq DiscreteQuotient.fiber_eq
-/

#print DiscreteQuotient.proj_surjective /-
theorem proj_surjective : Function.Surjective S.proj :=
  Quotient.surjective_Quotient_mk''
#align discrete_quotient.proj_surjective DiscreteQuotient.proj_surjective
-/

#print DiscreteQuotient.proj_quotientMap /-
theorem proj_quotientMap : QuotientMap S.proj :=
  quotientMap_quot_mk
#align discrete_quotient.proj_quotient_map DiscreteQuotient.proj_quotientMap
-/

#print DiscreteQuotient.proj_continuous /-
theorem proj_continuous : Continuous S.proj :=
  S.proj_quotientMap.Continuous
#align discrete_quotient.proj_continuous DiscreteQuotient.proj_continuous
-/

instance : DiscreteTopology S :=
  singletons_open_iff_discrete.1 <|
    S.proj_surjective.forall.2 fun x =>
      by
      rw [← S.proj_quotient_map.is_open_preimage, fiber_eq]
      exact S.is_open_set_of_rel _

#print DiscreteQuotient.proj_isLocallyConstant /-
theorem proj_isLocallyConstant : IsLocallyConstant S.proj :=
  (IsLocallyConstant.iff_continuous S.proj).2 S.proj_continuous
#align discrete_quotient.proj_is_locally_constant DiscreteQuotient.proj_isLocallyConstant
-/

#print DiscreteQuotient.isClopen_preimage /-
theorem isClopen_preimage (A : Set S) : IsClopen (S.proj ⁻¹' A) :=
  (isClopen_discrete A).Preimage S.proj_continuous
#align discrete_quotient.is_clopen_preimage DiscreteQuotient.isClopen_preimage
-/

#print DiscreteQuotient.isOpen_preimage /-
theorem isOpen_preimage (A : Set S) : IsOpen (S.proj ⁻¹' A) :=
  (S.isClopen_preimage A).1
#align discrete_quotient.is_open_preimage DiscreteQuotient.isOpen_preimage
-/

#print DiscreteQuotient.isClosed_preimage /-
theorem isClosed_preimage (A : Set S) : IsClosed (S.proj ⁻¹' A) :=
  (S.isClopen_preimage A).2
#align discrete_quotient.is_closed_preimage DiscreteQuotient.isClosed_preimage
-/

#print DiscreteQuotient.isClopen_setOf_rel /-
theorem isClopen_setOf_rel (x : X) : IsClopen (setOf (S.Rel x)) :=
  by
  rw [← fiber_eq]
  apply is_clopen_preimage
#align discrete_quotient.is_clopen_set_of_rel DiscreteQuotient.isClopen_setOf_rel
-/

instance : HasInf (DiscreteQuotient X) :=
  ⟨fun S₁ S₂ => ⟨S₁.1 ⊓ S₂.1, fun x => (S₁.2 x).inter (S₂.2 x)⟩⟩

instance : SemilatticeInf (DiscreteQuotient X) :=
  Injective.semilatticeInf toSetoid ext fun _ _ => rfl

instance : OrderTop (DiscreteQuotient X)
    where
  top := ⟨⊤, fun _ => isOpen_univ⟩
  le_top a := by tauto

instance : Inhabited (DiscreteQuotient X) :=
  ⟨⊤⟩

#print DiscreteQuotient.inhabitedQuotient /-
instance inhabitedQuotient [Inhabited X] : Inhabited S :=
  ⟨S.proj default⟩
#align discrete_quotient.inhabited_quotient DiscreteQuotient.inhabitedQuotient
-/

instance [Nonempty X] : Nonempty S :=
  Nonempty.map S.proj ‹_›

section Comap

variable (g : C(Y, Z)) (f : C(X, Y))

#print DiscreteQuotient.comap /-
/-- Comap a discrete quotient along a continuous map. -/
def comap (S : DiscreteQuotient Y) : DiscreteQuotient X
    where
  toSetoid := Setoid.comap f S.1
  isOpen_setOf_rel y := (S.2 _).Preimage f.Continuous
#align discrete_quotient.comap DiscreteQuotient.comap
-/

#print DiscreteQuotient.comap_id /-
@[simp]
theorem comap_id : S.comap (ContinuousMap.id X) = S :=
  by
  ext
  rfl
#align discrete_quotient.comap_id DiscreteQuotient.comap_id
-/

/- warning: discrete_quotient.comap_comp -> DiscreteQuotient.comap_comp is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u3} Z] (g : ContinuousMap.{u2, u3} Y Z _inst_2 _inst_3) (f : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (S : DiscreteQuotient.{u3} Z _inst_3), Eq.{succ u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.comap.{u1, u3} X Z _inst_1 _inst_3 (ContinuousMap.comp.{u1, u2, u3} X Y Z _inst_1 _inst_2 _inst_3 g f) S) (DiscreteQuotient.comap.{u1, u2} X Y _inst_1 _inst_2 f (DiscreteQuotient.comap.{u2, u3} Y Z _inst_2 _inst_3 g S))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] [_inst_3 : TopologicalSpace.{u3} Z] (g : ContinuousMap.{u1, u3} Y Z _inst_2 _inst_3) (f : ContinuousMap.{u2, u1} X Y _inst_1 _inst_2) (S : DiscreteQuotient.{u3} Z _inst_3), Eq.{succ u2} (DiscreteQuotient.{u2} X _inst_1) (DiscreteQuotient.comap.{u2, u3} X Z _inst_1 _inst_3 (ContinuousMap.comp.{u2, u1, u3} X Y Z _inst_1 _inst_2 _inst_3 g f) S) (DiscreteQuotient.comap.{u2, u1} X Y _inst_1 _inst_2 f (DiscreteQuotient.comap.{u1, u3} Y Z _inst_2 _inst_3 g S))
Case conversion may be inaccurate. Consider using '#align discrete_quotient.comap_comp DiscreteQuotient.comap_compₓ'. -/
@[simp]
theorem comap_comp (S : DiscreteQuotient Z) : S.comap (g.comp f) = (S.comap g).comap f :=
  rfl
#align discrete_quotient.comap_comp DiscreteQuotient.comap_comp

/- warning: discrete_quotient.comap_mono -> DiscreteQuotient.comap_mono is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (f : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) {A : DiscreteQuotient.{u2} Y _inst_2} {B : DiscreteQuotient.{u2} Y _inst_2}, (LE.le.{u2} (DiscreteQuotient.{u2} Y _inst_2) (Preorder.toLE.{u2} (DiscreteQuotient.{u2} Y _inst_2) (PartialOrder.toPreorder.{u2} (DiscreteQuotient.{u2} Y _inst_2) (SemilatticeInf.toPartialOrder.{u2} (DiscreteQuotient.{u2} Y _inst_2) (DiscreteQuotient.semilatticeInf.{u2} Y _inst_2)))) A B) -> (LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) (DiscreteQuotient.comap.{u1, u2} X Y _inst_1 _inst_2 f A) (DiscreteQuotient.comap.{u1, u2} X Y _inst_1 _inst_2 f B))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (f : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) {A : DiscreteQuotient.{u2} Y _inst_2} {B : DiscreteQuotient.{u2} Y _inst_2}, (LE.le.{u2} (DiscreteQuotient.{u2} Y _inst_2) (Preorder.toLE.{u2} (DiscreteQuotient.{u2} Y _inst_2) (PartialOrder.toPreorder.{u2} (DiscreteQuotient.{u2} Y _inst_2) (SemilatticeInf.toPartialOrder.{u2} (DiscreteQuotient.{u2} Y _inst_2) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u2} Y _inst_2)))) A B) -> (LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) (DiscreteQuotient.comap.{u1, u2} X Y _inst_1 _inst_2 f A) (DiscreteQuotient.comap.{u1, u2} X Y _inst_1 _inst_2 f B))
Case conversion may be inaccurate. Consider using '#align discrete_quotient.comap_mono DiscreteQuotient.comap_monoₓ'. -/
@[mono]
theorem comap_mono {A B : DiscreteQuotient Y} (h : A ≤ B) : A.comap f ≤ B.comap f := by tauto
#align discrete_quotient.comap_mono DiscreteQuotient.comap_mono

end Comap

section OfLe

variable {A B C : DiscreteQuotient X}

/- warning: discrete_quotient.of_le -> DiscreteQuotient.ofLe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u1} X _inst_1}, (LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) A B) -> (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A) -> (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) B)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u1} X _inst_1}, (LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) A B) -> (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 A)) -> (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 B))
Case conversion may be inaccurate. Consider using '#align discrete_quotient.of_le DiscreteQuotient.ofLeₓ'. -/
/-- The map induced by a refinement of a discrete quotient. -/
def ofLe (h : A ≤ B) : A → B :=
  Quotient.map' (fun x => x) h
#align discrete_quotient.of_le DiscreteQuotient.ofLe

#print DiscreteQuotient.ofLe_refl /-
@[simp]
theorem ofLe_refl : ofLe (le_refl A) = id := by
  ext ⟨⟩
  rfl
#align discrete_quotient.of_le_refl DiscreteQuotient.ofLe_refl
-/

#print DiscreteQuotient.ofLe_refl_apply /-
theorem ofLe_refl_apply (a : A) : ofLe (le_refl A) a = a := by simp
#align discrete_quotient.of_le_refl_apply DiscreteQuotient.ofLe_refl_apply
-/

/- warning: discrete_quotient.of_le_of_le -> DiscreteQuotient.ofLe_ofLe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u1} X _inst_1} {C : DiscreteQuotient.{u1} X _inst_1} (h₁ : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) A B) (h₂ : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) B C) (x : coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A), Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) C) (DiscreteQuotient.ofLe.{u1} X _inst_1 B C h₂ (DiscreteQuotient.ofLe.{u1} X _inst_1 A B h₁ x)) (DiscreteQuotient.ofLe.{u1} X _inst_1 A C (LE.le.trans.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1))) A B C h₁ h₂) x)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u1} X _inst_1} {C : DiscreteQuotient.{u1} X _inst_1} (h₁ : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) A B) (h₂ : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) B C) (x : Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 A)), Eq.{succ u1} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 C)) (DiscreteQuotient.ofLe.{u1} X _inst_1 B C h₂ (DiscreteQuotient.ofLe.{u1} X _inst_1 A B h₁ x)) (DiscreteQuotient.ofLe.{u1} X _inst_1 A C (LE.le.trans.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1))) A B C h₁ h₂) x)
Case conversion may be inaccurate. Consider using '#align discrete_quotient.of_le_of_le DiscreteQuotient.ofLe_ofLeₓ'. -/
@[simp]
theorem ofLe_ofLe (h₁ : A ≤ B) (h₂ : B ≤ C) (x : A) : ofLe h₂ (ofLe h₁ x) = ofLe (h₁.trans h₂) x :=
  by
  rcases x with ⟨⟩
  rfl
#align discrete_quotient.of_le_of_le DiscreteQuotient.ofLe_ofLe

/- warning: discrete_quotient.of_le_comp_of_le -> DiscreteQuotient.ofLe_comp_ofLe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u1} X _inst_1} {C : DiscreteQuotient.{u1} X _inst_1} (h₁ : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) A B) (h₂ : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) B C), Eq.{succ u1} ((coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A) -> (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) C)) (Function.comp.{succ u1, succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A) (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) B) (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) C) (DiscreteQuotient.ofLe.{u1} X _inst_1 B C h₂) (DiscreteQuotient.ofLe.{u1} X _inst_1 A B h₁)) (DiscreteQuotient.ofLe.{u1} X _inst_1 A C (le_trans.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1))) A B C h₁ h₂))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u1} X _inst_1} {C : DiscreteQuotient.{u1} X _inst_1} (h₁ : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) A B) (h₂ : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) B C), Eq.{succ u1} ((Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 A)) -> (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 C))) (Function.comp.{succ u1, succ u1, succ u1} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 A)) (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 B)) (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 C)) (DiscreteQuotient.ofLe.{u1} X _inst_1 B C h₂) (DiscreteQuotient.ofLe.{u1} X _inst_1 A B h₁)) (DiscreteQuotient.ofLe.{u1} X _inst_1 A C (le_trans.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1))) A B C h₁ h₂))
Case conversion may be inaccurate. Consider using '#align discrete_quotient.of_le_comp_of_le DiscreteQuotient.ofLe_comp_ofLeₓ'. -/
@[simp]
theorem ofLe_comp_ofLe (h₁ : A ≤ B) (h₂ : B ≤ C) : ofLe h₂ ∘ ofLe h₁ = ofLe (le_trans h₁ h₂) :=
  funext <| ofLe_ofLe _ _
#align discrete_quotient.of_le_comp_of_le DiscreteQuotient.ofLe_comp_ofLe

/- warning: discrete_quotient.of_le_continuous -> DiscreteQuotient.ofLe_continuous is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u1} X _inst_1} (h : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) A B), Continuous.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A) (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) B) (DiscreteQuotient.topologicalSpace.{u1} X _inst_1 A) (DiscreteQuotient.topologicalSpace.{u1} X _inst_1 B) (DiscreteQuotient.ofLe.{u1} X _inst_1 A B h)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u1} X _inst_1} (h : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) A B), Continuous.{u1, u1} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 A)) (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 B)) (DiscreteQuotient.instTopologicalSpaceQuotientToSetoid.{u1} X _inst_1 A) (DiscreteQuotient.instTopologicalSpaceQuotientToSetoid.{u1} X _inst_1 B) (DiscreteQuotient.ofLe.{u1} X _inst_1 A B h)
Case conversion may be inaccurate. Consider using '#align discrete_quotient.of_le_continuous DiscreteQuotient.ofLe_continuousₓ'. -/
theorem ofLe_continuous (h : A ≤ B) : Continuous (ofLe h) :=
  continuous_of_discreteTopology
#align discrete_quotient.of_le_continuous DiscreteQuotient.ofLe_continuous

/- warning: discrete_quotient.of_le_proj -> DiscreteQuotient.ofLe_proj is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u1} X _inst_1} (h : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) A B) (x : X), Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) B) (DiscreteQuotient.ofLe.{u1} X _inst_1 A B h (DiscreteQuotient.proj.{u1} X _inst_1 A x)) (DiscreteQuotient.proj.{u1} X _inst_1 B x)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u1} X _inst_1} (h : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) A B) (x : X), Eq.{succ u1} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 B)) (DiscreteQuotient.ofLe.{u1} X _inst_1 A B h (DiscreteQuotient.proj.{u1} X _inst_1 A x)) (DiscreteQuotient.proj.{u1} X _inst_1 B x)
Case conversion may be inaccurate. Consider using '#align discrete_quotient.of_le_proj DiscreteQuotient.ofLe_projₓ'. -/
@[simp]
theorem ofLe_proj (h : A ≤ B) (x : X) : ofLe h (A.proj x) = B.proj x :=
  Quotient.sound' (B.refl _)
#align discrete_quotient.of_le_proj DiscreteQuotient.ofLe_proj

/- warning: discrete_quotient.of_le_comp_proj -> DiscreteQuotient.ofLe_comp_proj is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u1} X _inst_1} (h : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) A B), Eq.{succ u1} (X -> (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) B)) (Function.comp.{succ u1, succ u1, succ u1} X (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A) (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) B) (DiscreteQuotient.ofLe.{u1} X _inst_1 A B h) (DiscreteQuotient.proj.{u1} X _inst_1 A)) (DiscreteQuotient.proj.{u1} X _inst_1 B)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u1} X _inst_1} (h : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) A B), Eq.{succ u1} (X -> (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 B))) (Function.comp.{succ u1, succ u1, succ u1} X (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 A)) (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 B)) (DiscreteQuotient.ofLe.{u1} X _inst_1 A B h) (DiscreteQuotient.proj.{u1} X _inst_1 A)) (DiscreteQuotient.proj.{u1} X _inst_1 B)
Case conversion may be inaccurate. Consider using '#align discrete_quotient.of_le_comp_proj DiscreteQuotient.ofLe_comp_projₓ'. -/
@[simp]
theorem ofLe_comp_proj (h : A ≤ B) : ofLe h ∘ A.proj = B.proj :=
  funext <| ofLe_proj _
#align discrete_quotient.of_le_comp_proj DiscreteQuotient.ofLe_comp_proj

end OfLe

/-- When `X` is a locally connected space, there is an `order_bot` instance on
`discrete_quotient X`. The bottom element is given by `connected_component_setoid X`
-/
instance [LocallyConnectedSpace X] : OrderBot (DiscreteQuotient X)
    where
  bot :=
    { toSetoid := connectedComponentSetoid X
      isOpen_setOf_rel := fun x =>
        by
        have : connectedComponent x = { y | (connectedComponentSetoid X).Rel x y } :=
          by
          ext y
          simpa only [connectedComponentSetoid, ← connectedComponent_eq_iff_mem] using eq_comm
        rw [← this]
        exact isOpen_connectedComponent }
  bot_le S x y (h : connectedComponent x = connectedComponent y) :=
    (S.isClopen_setOf_rel x).connectedComponent_subset (S.refl _) <| h.symm ▸ mem_connectedComponent

/- warning: discrete_quotient.proj_bot_eq -> DiscreteQuotient.proj_bot_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : LocallyConnectedSpace.{u1} X _inst_1] {x : X} {y : X}, Iff (Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toHasBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) (DiscreteQuotient.orderBot.{u1} X _inst_1 _inst_4)))) (DiscreteQuotient.proj.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toHasBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) (DiscreteQuotient.orderBot.{u1} X _inst_1 _inst_4))) x) (DiscreteQuotient.proj.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toHasBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) (DiscreteQuotient.orderBot.{u1} X _inst_1 _inst_4))) y)) (Eq.{succ u1} (Set.{u1} X) (connectedComponent.{u1} X _inst_1 x) (connectedComponent.{u1} X _inst_1 y))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : LocallyConnectedSpace.{u1} X _inst_1] {x : X} {y : X}, Iff (Eq.{succ u1} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) (DiscreteQuotient.instOrderBotDiscreteQuotientToLEToPreorderToPartialOrderInstSemilatticeInfDiscreteQuotient.{u1} X _inst_1 _inst_4))))) (DiscreteQuotient.proj.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) (DiscreteQuotient.instOrderBotDiscreteQuotientToLEToPreorderToPartialOrderInstSemilatticeInfDiscreteQuotient.{u1} X _inst_1 _inst_4))) x) (DiscreteQuotient.proj.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) (DiscreteQuotient.instOrderBotDiscreteQuotientToLEToPreorderToPartialOrderInstSemilatticeInfDiscreteQuotient.{u1} X _inst_1 _inst_4))) y)) (Eq.{succ u1} (Set.{u1} X) (connectedComponent.{u1} X _inst_1 x) (connectedComponent.{u1} X _inst_1 y))
Case conversion may be inaccurate. Consider using '#align discrete_quotient.proj_bot_eq DiscreteQuotient.proj_bot_eqₓ'. -/
@[simp]
theorem proj_bot_eq [LocallyConnectedSpace X] {x y : X} :
    proj ⊥ x = proj ⊥ y ↔ connectedComponent x = connectedComponent y :=
  Quotient.eq''
#align discrete_quotient.proj_bot_eq DiscreteQuotient.proj_bot_eq

/- warning: discrete_quotient.proj_bot_inj -> DiscreteQuotient.proj_bot_inj is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : DiscreteTopology.{u1} X _inst_1] {x : X} {y : X}, Iff (Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toHasBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) (DiscreteQuotient.orderBot.{u1} X _inst_1 (DiscreteTopology.toLocallyConnectedSpace.{u1} X _inst_1 _inst_4))))) (DiscreteQuotient.proj.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toHasBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) (DiscreteQuotient.orderBot.{u1} X _inst_1 (DiscreteTopology.toLocallyConnectedSpace.{u1} X _inst_1 _inst_4)))) x) (DiscreteQuotient.proj.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toHasBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) (DiscreteQuotient.orderBot.{u1} X _inst_1 (DiscreteTopology.toLocallyConnectedSpace.{u1} X _inst_1 _inst_4)))) y)) (Eq.{succ u1} X x y)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : DiscreteTopology.{u1} X _inst_1] {x : X} {y : X}, Iff (Eq.{succ u1} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) (DiscreteQuotient.instOrderBotDiscreteQuotientToLEToPreorderToPartialOrderInstSemilatticeInfDiscreteQuotient.{u1} X _inst_1 (DiscreteTopology.toLocallyConnectedSpace.{u1} X _inst_1 _inst_4)))))) (DiscreteQuotient.proj.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) (DiscreteQuotient.instOrderBotDiscreteQuotientToLEToPreorderToPartialOrderInstSemilatticeInfDiscreteQuotient.{u1} X _inst_1 (DiscreteTopology.toLocallyConnectedSpace.{u1} X _inst_1 _inst_4)))) x) (DiscreteQuotient.proj.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) (DiscreteQuotient.instOrderBotDiscreteQuotientToLEToPreorderToPartialOrderInstSemilatticeInfDiscreteQuotient.{u1} X _inst_1 (DiscreteTopology.toLocallyConnectedSpace.{u1} X _inst_1 _inst_4)))) y)) (Eq.{succ u1} X x y)
Case conversion may be inaccurate. Consider using '#align discrete_quotient.proj_bot_inj DiscreteQuotient.proj_bot_injₓ'. -/
theorem proj_bot_inj [DiscreteTopology X] {x y : X} : proj ⊥ x = proj ⊥ y ↔ x = y := by simp
#align discrete_quotient.proj_bot_inj DiscreteQuotient.proj_bot_inj

/- warning: discrete_quotient.proj_bot_injective -> DiscreteQuotient.proj_bot_injective is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : DiscreteTopology.{u1} X _inst_1], Function.Injective.{succ u1, succ u1} X (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toHasBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) (DiscreteQuotient.orderBot.{u1} X _inst_1 (DiscreteTopology.toLocallyConnectedSpace.{u1} X _inst_1 _inst_4))))) (DiscreteQuotient.proj.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toHasBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) (DiscreteQuotient.orderBot.{u1} X _inst_1 (DiscreteTopology.toLocallyConnectedSpace.{u1} X _inst_1 _inst_4)))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : DiscreteTopology.{u1} X _inst_1], Function.Injective.{succ u1, succ u1} X (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) (DiscreteQuotient.instOrderBotDiscreteQuotientToLEToPreorderToPartialOrderInstSemilatticeInfDiscreteQuotient.{u1} X _inst_1 (DiscreteTopology.toLocallyConnectedSpace.{u1} X _inst_1 _inst_4)))))) (DiscreteQuotient.proj.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) (DiscreteQuotient.instOrderBotDiscreteQuotientToLEToPreorderToPartialOrderInstSemilatticeInfDiscreteQuotient.{u1} X _inst_1 (DiscreteTopology.toLocallyConnectedSpace.{u1} X _inst_1 _inst_4)))))
Case conversion may be inaccurate. Consider using '#align discrete_quotient.proj_bot_injective DiscreteQuotient.proj_bot_injectiveₓ'. -/
theorem proj_bot_injective [DiscreteTopology X] : Injective (⊥ : DiscreteQuotient X).proj :=
  fun _ _ => proj_bot_inj.1
#align discrete_quotient.proj_bot_injective DiscreteQuotient.proj_bot_injective

/- warning: discrete_quotient.proj_bot_bijective -> DiscreteQuotient.proj_bot_bijective is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : DiscreteTopology.{u1} X _inst_1], Function.Bijective.{succ u1, succ u1} X (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toHasBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) (DiscreteQuotient.orderBot.{u1} X _inst_1 (DiscreteTopology.toLocallyConnectedSpace.{u1} X _inst_1 _inst_4))))) (DiscreteQuotient.proj.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toHasBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) (DiscreteQuotient.orderBot.{u1} X _inst_1 (DiscreteTopology.toLocallyConnectedSpace.{u1} X _inst_1 _inst_4)))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : DiscreteTopology.{u1} X _inst_1], Function.Bijective.{succ u1, succ u1} X (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) (DiscreteQuotient.instOrderBotDiscreteQuotientToLEToPreorderToPartialOrderInstSemilatticeInfDiscreteQuotient.{u1} X _inst_1 (DiscreteTopology.toLocallyConnectedSpace.{u1} X _inst_1 _inst_4)))))) (DiscreteQuotient.proj.{u1} X _inst_1 (Bot.bot.{u1} (DiscreteQuotient.{u1} X _inst_1) (OrderBot.toBot.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) (DiscreteQuotient.instOrderBotDiscreteQuotientToLEToPreorderToPartialOrderInstSemilatticeInfDiscreteQuotient.{u1} X _inst_1 (DiscreteTopology.toLocallyConnectedSpace.{u1} X _inst_1 _inst_4)))))
Case conversion may be inaccurate. Consider using '#align discrete_quotient.proj_bot_bijective DiscreteQuotient.proj_bot_bijectiveₓ'. -/
theorem proj_bot_bijective [DiscreteTopology X] : Bijective (⊥ : DiscreteQuotient X).proj :=
  ⟨proj_bot_injective, proj_surjective _⟩
#align discrete_quotient.proj_bot_bijective DiscreteQuotient.proj_bot_bijective

section Map

variable (f : C(X, Y)) (A A' : DiscreteQuotient X) (B B' : DiscreteQuotient Y)

#print DiscreteQuotient.LeComap /-
/-- Given `f : C(X, Y)`, `le_comap cont A B` is defined as `A ≤ B.comap f`. Mathematically this
means that `f` descends to a morphism `A → B`. -/
def LeComap : Prop :=
  A ≤ B.comap f
#align discrete_quotient.le_comap DiscreteQuotient.LeComap
-/

#print DiscreteQuotient.leComap_id /-
theorem leComap_id : LeComap (ContinuousMap.id X) A A := fun _ _ => id
#align discrete_quotient.le_comap_id DiscreteQuotient.leComap_id
-/

variable {A A' B B'} {f} {g : C(Y, Z)} {C : DiscreteQuotient Z}

/- warning: discrete_quotient.le_comap_id_iff -> DiscreteQuotient.leComap_id_iff is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {A' : DiscreteQuotient.{u1} X _inst_1}, Iff (DiscreteQuotient.LeComap.{u1, u1} X X _inst_1 _inst_1 (ContinuousMap.id.{u1} X _inst_1) A A') (LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) A A')
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {A' : DiscreteQuotient.{u1} X _inst_1}, Iff (DiscreteQuotient.LeComap.{u1, u1} X X _inst_1 _inst_1 (ContinuousMap.id.{u1} X _inst_1) A A') (LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) A A')
Case conversion may be inaccurate. Consider using '#align discrete_quotient.le_comap_id_iff DiscreteQuotient.leComap_id_iffₓ'. -/
@[simp]
theorem leComap_id_iff : LeComap (ContinuousMap.id X) A A' ↔ A ≤ A' :=
  Iff.rfl
#align discrete_quotient.le_comap_id_iff DiscreteQuotient.leComap_id_iff

/- warning: discrete_quotient.le_comap.comp -> DiscreteQuotient.LeComap.comp is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u3} Z] {f : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u2} Y _inst_2} {g : ContinuousMap.{u2, u3} Y Z _inst_2 _inst_3} {C : DiscreteQuotient.{u3} Z _inst_3}, (DiscreteQuotient.LeComap.{u2, u3} Y Z _inst_2 _inst_3 g B C) -> (DiscreteQuotient.LeComap.{u1, u2} X Y _inst_1 _inst_2 f A B) -> (DiscreteQuotient.LeComap.{u1, u3} X Z _inst_1 _inst_3 (ContinuousMap.comp.{u1, u2, u3} X Y Z _inst_1 _inst_2 _inst_3 g f) A C)
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u3}} {Z : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} Y] [_inst_3 : TopologicalSpace.{u2} Z] {f : ContinuousMap.{u1, u3} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u3} Y _inst_2} {g : ContinuousMap.{u3, u2} Y Z _inst_2 _inst_3} {C : DiscreteQuotient.{u2} Z _inst_3}, (DiscreteQuotient.LeComap.{u3, u2} Y Z _inst_2 _inst_3 g B C) -> (DiscreteQuotient.LeComap.{u1, u3} X Y _inst_1 _inst_2 f A B) -> (DiscreteQuotient.LeComap.{u1, u2} X Z _inst_1 _inst_3 (ContinuousMap.comp.{u1, u3, u2} X Y Z _inst_1 _inst_2 _inst_3 g f) A C)
Case conversion may be inaccurate. Consider using '#align discrete_quotient.le_comap.comp DiscreteQuotient.LeComap.compₓ'. -/
theorem LeComap.comp : LeComap g B C → LeComap f A B → LeComap (g.comp f) A C := by tauto
#align discrete_quotient.le_comap.comp DiscreteQuotient.LeComap.comp

/- warning: discrete_quotient.le_comap.mono -> DiscreteQuotient.LeComap.mono is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u1} X _inst_1} {A' : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u2} Y _inst_2} {B' : DiscreteQuotient.{u2} Y _inst_2}, (DiscreteQuotient.LeComap.{u1, u2} X Y _inst_1 _inst_2 f A B) -> (LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) A' A) -> (LE.le.{u2} (DiscreteQuotient.{u2} Y _inst_2) (Preorder.toLE.{u2} (DiscreteQuotient.{u2} Y _inst_2) (PartialOrder.toPreorder.{u2} (DiscreteQuotient.{u2} Y _inst_2) (SemilatticeInf.toPartialOrder.{u2} (DiscreteQuotient.{u2} Y _inst_2) (DiscreteQuotient.semilatticeInf.{u2} Y _inst_2)))) B B') -> (DiscreteQuotient.LeComap.{u1, u2} X Y _inst_1 _inst_2 f A' B')
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : ContinuousMap.{u2, u1} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u2} X _inst_1} {A' : DiscreteQuotient.{u2} X _inst_1} {B : DiscreteQuotient.{u1} Y _inst_2} {B' : DiscreteQuotient.{u1} Y _inst_2}, (DiscreteQuotient.LeComap.{u2, u1} X Y _inst_1 _inst_2 f A B) -> (LE.le.{u2} (DiscreteQuotient.{u2} X _inst_1) (Preorder.toLE.{u2} (DiscreteQuotient.{u2} X _inst_1) (PartialOrder.toPreorder.{u2} (DiscreteQuotient.{u2} X _inst_1) (SemilatticeInf.toPartialOrder.{u2} (DiscreteQuotient.{u2} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u2} X _inst_1)))) A' A) -> (LE.le.{u1} (DiscreteQuotient.{u1} Y _inst_2) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} Y _inst_2) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} Y _inst_2) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} Y _inst_2) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} Y _inst_2)))) B B') -> (DiscreteQuotient.LeComap.{u2, u1} X Y _inst_1 _inst_2 f A' B')
Case conversion may be inaccurate. Consider using '#align discrete_quotient.le_comap.mono DiscreteQuotient.LeComap.monoₓ'. -/
theorem LeComap.mono (h : LeComap f A B) (hA : A' ≤ A) (hB : B ≤ B') : LeComap f A' B' :=
  hA.trans <| le_trans h <| comap_mono _ hB
#align discrete_quotient.le_comap.mono DiscreteQuotient.LeComap.mono

#print DiscreteQuotient.map /-
/-- Map a discrete quotient along a continuous map. -/
def map (f : C(X, Y)) (cond : LeComap f A B) : A → B :=
  Quotient.map' f cond
#align discrete_quotient.map DiscreteQuotient.map
-/

/- warning: discrete_quotient.map_continuous -> DiscreteQuotient.map_continuous is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u2} Y _inst_2} (cond : DiscreteQuotient.LeComap.{u1, u2} X Y _inst_1 _inst_2 f A B), Continuous.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A) (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} Y _inst_2) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} Y _inst_2) B) (DiscreteQuotient.topologicalSpace.{u1} X _inst_1 A) (DiscreteQuotient.topologicalSpace.{u2} Y _inst_2 B) (DiscreteQuotient.map.{u1, u2} X Y _inst_1 _inst_2 A B f cond)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : ContinuousMap.{u2, u1} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u2} X _inst_1} {B : DiscreteQuotient.{u1} Y _inst_2} (cond : DiscreteQuotient.LeComap.{u2, u1} X Y _inst_1 _inst_2 f A B), Continuous.{u2, u1} (Quotient.{succ u2} X (DiscreteQuotient.toSetoid.{u2} X _inst_1 A)) (Quotient.{succ u1} Y (DiscreteQuotient.toSetoid.{u1} Y _inst_2 B)) (DiscreteQuotient.instTopologicalSpaceQuotientToSetoid.{u2} X _inst_1 A) (DiscreteQuotient.instTopologicalSpaceQuotientToSetoid.{u1} Y _inst_2 B) (DiscreteQuotient.map.{u2, u1} X Y _inst_1 _inst_2 A B f cond)
Case conversion may be inaccurate. Consider using '#align discrete_quotient.map_continuous DiscreteQuotient.map_continuousₓ'. -/
theorem map_continuous (cond : LeComap f A B) : Continuous (map f cond) :=
  continuous_of_discreteTopology
#align discrete_quotient.map_continuous DiscreteQuotient.map_continuous

/- warning: discrete_quotient.map_comp_proj -> DiscreteQuotient.map_comp_proj is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u2} Y _inst_2} (cond : DiscreteQuotient.LeComap.{u1, u2} X Y _inst_1 _inst_2 f A B), Eq.{max (succ u1) (succ u2)} (X -> (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} Y _inst_2) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} Y _inst_2) B)) (Function.comp.{succ u1, succ u1, succ u2} X (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A) (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} Y _inst_2) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} Y _inst_2) B) (DiscreteQuotient.map.{u1, u2} X Y _inst_1 _inst_2 A B f cond) (DiscreteQuotient.proj.{u1} X _inst_1 A)) (Function.comp.{succ u1, succ u2, succ u2} X Y (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} Y _inst_2) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} Y _inst_2) B) (DiscreteQuotient.proj.{u2} Y _inst_2 B) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) => X -> Y) (ContinuousMap.hasCoeToFun.{u1, u2} X Y _inst_1 _inst_2) f))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : ContinuousMap.{u2, u1} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u2} X _inst_1} {B : DiscreteQuotient.{u1} Y _inst_2} (cond : DiscreteQuotient.LeComap.{u2, u1} X Y _inst_1 _inst_2 f A B), Eq.{max (succ u2) (succ u1)} (X -> (Quotient.{succ u1} Y (DiscreteQuotient.toSetoid.{u1} Y _inst_2 B))) (Function.comp.{succ u2, succ u2, succ u1} X (Quotient.{succ u2} X (DiscreteQuotient.toSetoid.{u2} X _inst_1 A)) (Quotient.{succ u1} Y (DiscreteQuotient.toSetoid.{u1} Y _inst_2 B)) (DiscreteQuotient.map.{u2, u1} X Y _inst_1 _inst_2 A B f cond) (DiscreteQuotient.proj.{u2} X _inst_1 A)) (Function.comp.{succ u2, succ u1, succ u1} X Y (Quotient.{succ u1} Y (DiscreteQuotient.toSetoid.{u1} Y _inst_2 B)) (DiscreteQuotient.proj.{u1} Y _inst_2 B) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} X Y _inst_1 _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : X) => Y) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} X Y _inst_1 _inst_2) X Y _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} X Y _inst_1 _inst_2)) f))
Case conversion may be inaccurate. Consider using '#align discrete_quotient.map_comp_proj DiscreteQuotient.map_comp_projₓ'. -/
@[simp]
theorem map_comp_proj (cond : LeComap f A B) : map f cond ∘ A.proj = B.proj ∘ f :=
  rfl
#align discrete_quotient.map_comp_proj DiscreteQuotient.map_comp_proj

/- warning: discrete_quotient.map_proj -> DiscreteQuotient.map_proj is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u2} Y _inst_2} (cond : DiscreteQuotient.LeComap.{u1, u2} X Y _inst_1 _inst_2 f A B) (x : X), Eq.{succ u2} (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} Y _inst_2) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} Y _inst_2) B) (DiscreteQuotient.map.{u1, u2} X Y _inst_1 _inst_2 A B f cond (DiscreteQuotient.proj.{u1} X _inst_1 A x)) (DiscreteQuotient.proj.{u2} Y _inst_2 B (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) => X -> Y) (ContinuousMap.hasCoeToFun.{u1, u2} X Y _inst_1 _inst_2) f x))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : ContinuousMap.{u2, u1} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u2} X _inst_1} {B : DiscreteQuotient.{u1} Y _inst_2} (cond : DiscreteQuotient.LeComap.{u2, u1} X Y _inst_1 _inst_2 f A B) (x : X), Eq.{succ u1} (Quotient.{succ u1} Y (DiscreteQuotient.toSetoid.{u1} Y _inst_2 B)) (DiscreteQuotient.map.{u2, u1} X Y _inst_1 _inst_2 A B f cond (DiscreteQuotient.proj.{u2} X _inst_1 A x)) (DiscreteQuotient.proj.{u1} Y _inst_2 B (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} X Y _inst_1 _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : X) => Y) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} X Y _inst_1 _inst_2) X Y _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} X Y _inst_1 _inst_2)) f x))
Case conversion may be inaccurate. Consider using '#align discrete_quotient.map_proj DiscreteQuotient.map_projₓ'. -/
@[simp]
theorem map_proj (cond : LeComap f A B) (x : X) : map f cond (A.proj x) = B.proj (f x) :=
  rfl
#align discrete_quotient.map_proj DiscreteQuotient.map_proj

#print DiscreteQuotient.map_id /-
@[simp]
theorem map_id : map _ (leComap_id A) = id := by ext ⟨⟩ <;> rfl
#align discrete_quotient.map_id DiscreteQuotient.map_id
-/

/- warning: discrete_quotient.map_comp -> DiscreteQuotient.map_comp is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u3} Z] {f : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u2} Y _inst_2} {g : ContinuousMap.{u2, u3} Y Z _inst_2 _inst_3} {C : DiscreteQuotient.{u3} Z _inst_3} (h1 : DiscreteQuotient.LeComap.{u2, u3} Y Z _inst_2 _inst_3 g B C) (h2 : DiscreteQuotient.LeComap.{u1, u2} X Y _inst_1 _inst_2 f A B), Eq.{max (succ u1) (succ u3)} ((coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A) -> (coeSort.{succ u3, succ (succ u3)} (DiscreteQuotient.{u3} Z _inst_3) Type.{u3} (DiscreteQuotient.hasCoeToSort.{u3} Z _inst_3) C)) (DiscreteQuotient.map.{u1, u3} X Z _inst_1 _inst_3 A C (ContinuousMap.comp.{u1, u2, u3} X Y Z _inst_1 _inst_2 _inst_3 g f) (DiscreteQuotient.LeComap.comp.{u1, u2, u3} X Y Z _inst_1 _inst_2 _inst_3 f A B g C h1 h2)) (Function.comp.{succ u1, succ u2, succ u3} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A) (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} Y _inst_2) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} Y _inst_2) B) (coeSort.{succ u3, succ (succ u3)} (DiscreteQuotient.{u3} Z _inst_3) Type.{u3} (DiscreteQuotient.hasCoeToSort.{u3} Z _inst_3) C) (DiscreteQuotient.map.{u2, u3} Y Z _inst_2 _inst_3 B C g h1) (DiscreteQuotient.map.{u1, u2} X Y _inst_1 _inst_2 A B f h2))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u3}} {Z : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} Y] [_inst_3 : TopologicalSpace.{u2} Z] {f : ContinuousMap.{u1, u3} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u3} Y _inst_2} {g : ContinuousMap.{u3, u2} Y Z _inst_2 _inst_3} {C : DiscreteQuotient.{u2} Z _inst_3} (h1 : DiscreteQuotient.LeComap.{u3, u2} Y Z _inst_2 _inst_3 g B C) (h2 : DiscreteQuotient.LeComap.{u1, u3} X Y _inst_1 _inst_2 f A B), Eq.{max (succ u1) (succ u2)} ((Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 A)) -> (Quotient.{succ u2} Z (DiscreteQuotient.toSetoid.{u2} Z _inst_3 C))) (DiscreteQuotient.map.{u1, u2} X Z _inst_1 _inst_3 A C (ContinuousMap.comp.{u1, u3, u2} X Y Z _inst_1 _inst_2 _inst_3 g f) (DiscreteQuotient.LeComap.comp.{u1, u2, u3} X Y Z _inst_1 _inst_2 _inst_3 f A B g C h1 h2)) (Function.comp.{succ u1, succ u3, succ u2} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 A)) (Quotient.{succ u3} Y (DiscreteQuotient.toSetoid.{u3} Y _inst_2 B)) (Quotient.{succ u2} Z (DiscreteQuotient.toSetoid.{u2} Z _inst_3 C)) (DiscreteQuotient.map.{u3, u2} Y Z _inst_2 _inst_3 B C g h1) (DiscreteQuotient.map.{u1, u3} X Y _inst_1 _inst_2 A B f h2))
Case conversion may be inaccurate. Consider using '#align discrete_quotient.map_comp DiscreteQuotient.map_compₓ'. -/
@[simp]
theorem map_comp (h1 : LeComap g B C) (h2 : LeComap f A B) :
    map (g.comp f) (h1.comp h2) = map g h1 ∘ map f h2 :=
  by
  ext ⟨⟩
  rfl
#align discrete_quotient.map_comp DiscreteQuotient.map_comp

/- warning: discrete_quotient.of_le_map -> DiscreteQuotient.ofLe_map is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u2} Y _inst_2} {B' : DiscreteQuotient.{u2} Y _inst_2} (cond : DiscreteQuotient.LeComap.{u1, u2} X Y _inst_1 _inst_2 f A B) (h : LE.le.{u2} (DiscreteQuotient.{u2} Y _inst_2) (Preorder.toLE.{u2} (DiscreteQuotient.{u2} Y _inst_2) (PartialOrder.toPreorder.{u2} (DiscreteQuotient.{u2} Y _inst_2) (SemilatticeInf.toPartialOrder.{u2} (DiscreteQuotient.{u2} Y _inst_2) (DiscreteQuotient.semilatticeInf.{u2} Y _inst_2)))) B B') (a : coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A), Eq.{succ u2} (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} Y _inst_2) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} Y _inst_2) B') (DiscreteQuotient.ofLe.{u2} Y _inst_2 B B' h (DiscreteQuotient.map.{u1, u2} X Y _inst_1 _inst_2 A B f cond a)) (DiscreteQuotient.map.{u1, u2} X Y _inst_1 _inst_2 A B' f (DiscreteQuotient.LeComap.mono.{u1, u2} X Y _inst_1 _inst_2 f A A B B' cond (le_rfl.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1))) A) h) a)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : ContinuousMap.{u2, u1} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u2} X _inst_1} {B : DiscreteQuotient.{u1} Y _inst_2} {B' : DiscreteQuotient.{u1} Y _inst_2} (cond : DiscreteQuotient.LeComap.{u2, u1} X Y _inst_1 _inst_2 f A B) (h : LE.le.{u1} (DiscreteQuotient.{u1} Y _inst_2) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} Y _inst_2) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} Y _inst_2) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} Y _inst_2) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} Y _inst_2)))) B B') (a : Quotient.{succ u2} X (DiscreteQuotient.toSetoid.{u2} X _inst_1 A)), Eq.{succ u1} (Quotient.{succ u1} Y (DiscreteQuotient.toSetoid.{u1} Y _inst_2 B')) (DiscreteQuotient.ofLe.{u1} Y _inst_2 B B' h (DiscreteQuotient.map.{u2, u1} X Y _inst_1 _inst_2 A B f cond a)) (DiscreteQuotient.map.{u2, u1} X Y _inst_1 _inst_2 A B' f (DiscreteQuotient.LeComap.mono.{u1, u2} X Y _inst_1 _inst_2 f A A B B' cond (le_rfl.{u2} (DiscreteQuotient.{u2} X _inst_1) (PartialOrder.toPreorder.{u2} (DiscreteQuotient.{u2} X _inst_1) (SemilatticeInf.toPartialOrder.{u2} (DiscreteQuotient.{u2} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u2} X _inst_1))) A) h) a)
Case conversion may be inaccurate. Consider using '#align discrete_quotient.of_le_map DiscreteQuotient.ofLe_mapₓ'. -/
@[simp]
theorem ofLe_map (cond : LeComap f A B) (h : B ≤ B') (a : A) :
    ofLe h (map f cond a) = map f (cond.mono le_rfl h) a :=
  by
  rcases a with ⟨⟩
  rfl
#align discrete_quotient.of_le_map DiscreteQuotient.ofLe_map

/- warning: discrete_quotient.of_le_comp_map -> DiscreteQuotient.ofLe_comp_map is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u2} Y _inst_2} {B' : DiscreteQuotient.{u2} Y _inst_2} (cond : DiscreteQuotient.LeComap.{u1, u2} X Y _inst_1 _inst_2 f A B) (h : LE.le.{u2} (DiscreteQuotient.{u2} Y _inst_2) (Preorder.toLE.{u2} (DiscreteQuotient.{u2} Y _inst_2) (PartialOrder.toPreorder.{u2} (DiscreteQuotient.{u2} Y _inst_2) (SemilatticeInf.toPartialOrder.{u2} (DiscreteQuotient.{u2} Y _inst_2) (DiscreteQuotient.semilatticeInf.{u2} Y _inst_2)))) B B'), Eq.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A) -> (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} Y _inst_2) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} Y _inst_2) B')) (Function.comp.{succ u1, succ u2, succ u2} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A) (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} Y _inst_2) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} Y _inst_2) B) (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} Y _inst_2) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} Y _inst_2) B') (DiscreteQuotient.ofLe.{u2} Y _inst_2 B B' h) (DiscreteQuotient.map.{u1, u2} X Y _inst_1 _inst_2 A B f cond)) (DiscreteQuotient.map.{u1, u2} X Y _inst_1 _inst_2 A B' f (DiscreteQuotient.LeComap.mono.{u1, u2} X Y _inst_1 _inst_2 f A A B B' cond (le_rfl.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1))) A) h))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : ContinuousMap.{u2, u1} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u2} X _inst_1} {B : DiscreteQuotient.{u1} Y _inst_2} {B' : DiscreteQuotient.{u1} Y _inst_2} (cond : DiscreteQuotient.LeComap.{u2, u1} X Y _inst_1 _inst_2 f A B) (h : LE.le.{u1} (DiscreteQuotient.{u1} Y _inst_2) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} Y _inst_2) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} Y _inst_2) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} Y _inst_2) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} Y _inst_2)))) B B'), Eq.{max (succ u2) (succ u1)} ((Quotient.{succ u2} X (DiscreteQuotient.toSetoid.{u2} X _inst_1 A)) -> (Quotient.{succ u1} Y (DiscreteQuotient.toSetoid.{u1} Y _inst_2 B'))) (Function.comp.{succ u2, succ u1, succ u1} (Quotient.{succ u2} X (DiscreteQuotient.toSetoid.{u2} X _inst_1 A)) (Quotient.{succ u1} Y (DiscreteQuotient.toSetoid.{u1} Y _inst_2 B)) (Quotient.{succ u1} Y (DiscreteQuotient.toSetoid.{u1} Y _inst_2 B')) (DiscreteQuotient.ofLe.{u1} Y _inst_2 B B' h) (DiscreteQuotient.map.{u2, u1} X Y _inst_1 _inst_2 A B f cond)) (DiscreteQuotient.map.{u2, u1} X Y _inst_1 _inst_2 A B' f (DiscreteQuotient.LeComap.mono.{u1, u2} X Y _inst_1 _inst_2 f A A B B' cond (le_rfl.{u2} (DiscreteQuotient.{u2} X _inst_1) (PartialOrder.toPreorder.{u2} (DiscreteQuotient.{u2} X _inst_1) (SemilatticeInf.toPartialOrder.{u2} (DiscreteQuotient.{u2} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u2} X _inst_1))) A) h))
Case conversion may be inaccurate. Consider using '#align discrete_quotient.of_le_comp_map DiscreteQuotient.ofLe_comp_mapₓ'. -/
@[simp]
theorem ofLe_comp_map (cond : LeComap f A B) (h : B ≤ B') :
    ofLe h ∘ map f cond = map f (cond.mono le_rfl h) :=
  funext <| ofLe_map cond h
#align discrete_quotient.of_le_comp_map DiscreteQuotient.ofLe_comp_map

/- warning: discrete_quotient.map_of_le -> DiscreteQuotient.map_ofLe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u1} X _inst_1} {A' : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u2} Y _inst_2} (cond : DiscreteQuotient.LeComap.{u1, u2} X Y _inst_1 _inst_2 f A B) (h : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) A' A) (c : coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A'), Eq.{succ u2} (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} Y _inst_2) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} Y _inst_2) B) (DiscreteQuotient.map.{u1, u2} X Y _inst_1 _inst_2 A B f cond (DiscreteQuotient.ofLe.{u1} X _inst_1 A' A h c)) (DiscreteQuotient.map.{u1, u2} X Y _inst_1 _inst_2 A' B f (DiscreteQuotient.LeComap.mono.{u1, u2} X Y _inst_1 _inst_2 f A A' B B cond h (le_rfl.{u2} (DiscreteQuotient.{u2} Y _inst_2) (PartialOrder.toPreorder.{u2} (DiscreteQuotient.{u2} Y _inst_2) (SemilatticeInf.toPartialOrder.{u2} (DiscreteQuotient.{u2} Y _inst_2) (DiscreteQuotient.semilatticeInf.{u2} Y _inst_2))) B)) c)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : ContinuousMap.{u2, u1} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u2} X _inst_1} {A' : DiscreteQuotient.{u2} X _inst_1} {B : DiscreteQuotient.{u1} Y _inst_2} (cond : DiscreteQuotient.LeComap.{u2, u1} X Y _inst_1 _inst_2 f A B) (h : LE.le.{u2} (DiscreteQuotient.{u2} X _inst_1) (Preorder.toLE.{u2} (DiscreteQuotient.{u2} X _inst_1) (PartialOrder.toPreorder.{u2} (DiscreteQuotient.{u2} X _inst_1) (SemilatticeInf.toPartialOrder.{u2} (DiscreteQuotient.{u2} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u2} X _inst_1)))) A' A) (c : Quotient.{succ u2} X (DiscreteQuotient.toSetoid.{u2} X _inst_1 A')), Eq.{succ u1} (Quotient.{succ u1} Y (DiscreteQuotient.toSetoid.{u1} Y _inst_2 B)) (DiscreteQuotient.map.{u2, u1} X Y _inst_1 _inst_2 A B f cond (DiscreteQuotient.ofLe.{u2} X _inst_1 A' A h c)) (DiscreteQuotient.map.{u2, u1} X Y _inst_1 _inst_2 A' B f (DiscreteQuotient.LeComap.mono.{u1, u2} X Y _inst_1 _inst_2 f A A' B B cond h (le_rfl.{u1} (DiscreteQuotient.{u1} Y _inst_2) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} Y _inst_2) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} Y _inst_2) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} Y _inst_2))) B)) c)
Case conversion may be inaccurate. Consider using '#align discrete_quotient.map_of_le DiscreteQuotient.map_ofLeₓ'. -/
@[simp]
theorem map_ofLe (cond : LeComap f A B) (h : A' ≤ A) (c : A') :
    map f cond (ofLe h c) = map f (cond.mono h le_rfl) c :=
  by
  rcases c with ⟨⟩
  rfl
#align discrete_quotient.map_of_le DiscreteQuotient.map_ofLe

/- warning: discrete_quotient.map_comp_of_le -> DiscreteQuotient.map_comp_ofLe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u1} X _inst_1} {A' : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u2} Y _inst_2} (cond : DiscreteQuotient.LeComap.{u1, u2} X Y _inst_1 _inst_2 f A B) (h : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) A' A), Eq.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A') -> (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} Y _inst_2) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} Y _inst_2) B)) (Function.comp.{succ u1, succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A') (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A) (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} Y _inst_2) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} Y _inst_2) B) (DiscreteQuotient.map.{u1, u2} X Y _inst_1 _inst_2 A B f cond) (DiscreteQuotient.ofLe.{u1} X _inst_1 A' A h)) (DiscreteQuotient.map.{u1, u2} X Y _inst_1 _inst_2 A' B f (DiscreteQuotient.LeComap.mono.{u1, u2} X Y _inst_1 _inst_2 f A A' B B cond h (le_rfl.{u2} (DiscreteQuotient.{u2} Y _inst_2) (PartialOrder.toPreorder.{u2} (DiscreteQuotient.{u2} Y _inst_2) (SemilatticeInf.toPartialOrder.{u2} (DiscreteQuotient.{u2} Y _inst_2) (DiscreteQuotient.semilatticeInf.{u2} Y _inst_2))) B)))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : ContinuousMap.{u2, u1} X Y _inst_1 _inst_2} {A : DiscreteQuotient.{u2} X _inst_1} {A' : DiscreteQuotient.{u2} X _inst_1} {B : DiscreteQuotient.{u1} Y _inst_2} (cond : DiscreteQuotient.LeComap.{u2, u1} X Y _inst_1 _inst_2 f A B) (h : LE.le.{u2} (DiscreteQuotient.{u2} X _inst_1) (Preorder.toLE.{u2} (DiscreteQuotient.{u2} X _inst_1) (PartialOrder.toPreorder.{u2} (DiscreteQuotient.{u2} X _inst_1) (SemilatticeInf.toPartialOrder.{u2} (DiscreteQuotient.{u2} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u2} X _inst_1)))) A' A), Eq.{max (succ u2) (succ u1)} ((Quotient.{succ u2} X (DiscreteQuotient.toSetoid.{u2} X _inst_1 A')) -> (Quotient.{succ u1} Y (DiscreteQuotient.toSetoid.{u1} Y _inst_2 B))) (Function.comp.{succ u2, succ u2, succ u1} (Quotient.{succ u2} X (DiscreteQuotient.toSetoid.{u2} X _inst_1 A')) (Quotient.{succ u2} X (DiscreteQuotient.toSetoid.{u2} X _inst_1 A)) (Quotient.{succ u1} Y (DiscreteQuotient.toSetoid.{u1} Y _inst_2 B)) (DiscreteQuotient.map.{u2, u1} X Y _inst_1 _inst_2 A B f cond) (DiscreteQuotient.ofLe.{u2} X _inst_1 A' A h)) (DiscreteQuotient.map.{u2, u1} X Y _inst_1 _inst_2 A' B f (DiscreteQuotient.LeComap.mono.{u1, u2} X Y _inst_1 _inst_2 f A A' B B cond h (le_rfl.{u1} (DiscreteQuotient.{u1} Y _inst_2) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} Y _inst_2) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} Y _inst_2) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} Y _inst_2))) B)))
Case conversion may be inaccurate. Consider using '#align discrete_quotient.map_comp_of_le DiscreteQuotient.map_comp_ofLeₓ'. -/
@[simp]
theorem map_comp_ofLe (cond : LeComap f A B) (h : A' ≤ A) :
    map f cond ∘ ofLe h = map f (cond.mono h le_rfl) :=
  funext <| map_ofLe cond h
#align discrete_quotient.map_comp_of_le DiscreteQuotient.map_comp_ofLe

end Map

#print DiscreteQuotient.eq_of_forall_proj_eq /-
theorem eq_of_forall_proj_eq [T2Space X] [CompactSpace X] [disc : TotallyDisconnectedSpace X]
    {x y : X} (h : ∀ Q : DiscreteQuotient X, Q.proj x = Q.proj y) : x = y :=
  by
  rw [← mem_singleton_iff, ← connectedComponent_eq_singleton, connectedComponent_eq_interᵢ_clopen,
    mem_Inter]
  rintro ⟨U, hU1, hU2⟩
  exact (Quotient.exact' (h (of_clopen hU1))).mpr hU2
#align discrete_quotient.eq_of_forall_proj_eq DiscreteQuotient.eq_of_forall_proj_eq
-/

/- warning: discrete_quotient.fiber_subset_of_le -> DiscreteQuotient.fiber_subset_ofLe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u1} X _inst_1} (h : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) A B) (a : coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A), HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) (Set.preimage.{u1, u1} X (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A) (DiscreteQuotient.proj.{u1} X _inst_1 A) (Singleton.singleton.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A) (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A)) (Set.hasSingleton.{u1} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) A)) a)) (Set.preimage.{u1, u1} X (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) B) (DiscreteQuotient.proj.{u1} X _inst_1 B) (Singleton.singleton.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) B) (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) B)) (Set.hasSingleton.{u1} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) B)) (DiscreteQuotient.ofLe.{u1} X _inst_1 A B h a)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {A : DiscreteQuotient.{u1} X _inst_1} {B : DiscreteQuotient.{u1} X _inst_1} (h : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) A B) (a : Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 A)), HasSubset.Subset.{u1} (Set.{u1} X) (Set.instHasSubsetSet.{u1} X) (Set.preimage.{u1, u1} X (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 A)) (DiscreteQuotient.proj.{u1} X _inst_1 A) (Singleton.singleton.{u1, u1} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 A)) (Set.{u1} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 A))) (Set.instSingletonSet.{u1} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 A))) a)) (Set.preimage.{u1, u1} X (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 B)) (DiscreteQuotient.proj.{u1} X _inst_1 B) (Singleton.singleton.{u1, u1} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 B)) (Set.{u1} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 B))) (Set.instSingletonSet.{u1} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 B))) (DiscreteQuotient.ofLe.{u1} X _inst_1 A B h a)))
Case conversion may be inaccurate. Consider using '#align discrete_quotient.fiber_subset_of_le DiscreteQuotient.fiber_subset_ofLeₓ'. -/
theorem fiber_subset_ofLe {A B : DiscreteQuotient X} (h : A ≤ B) (a : A) :
    A.proj ⁻¹' {a} ⊆ B.proj ⁻¹' {ofLe h a} :=
  by
  rcases A.proj_surjective a with ⟨a, rfl⟩
  rw [fiber_eq, of_le_proj, fiber_eq]
  exact fun _ h' => h h'
#align discrete_quotient.fiber_subset_of_le DiscreteQuotient.fiber_subset_ofLe

/- warning: discrete_quotient.exists_of_compat -> DiscreteQuotient.exists_of_compat is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : CompactSpace.{u1} X _inst_1] (Qs : forall (Q : DiscreteQuotient.{u1} X _inst_1), coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) Q), (forall (A : DiscreteQuotient.{u1} X _inst_1) (B : DiscreteQuotient.{u1} X _inst_1) (h : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.semilatticeInf.{u1} X _inst_1)))) A B), Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) B) (DiscreteQuotient.ofLe.{u1} X _inst_1 A B h (Qs A)) (Qs B)) -> (Exists.{succ u1} X (fun (x : X) => forall (Q : DiscreteQuotient.{u1} X _inst_1), Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (DiscreteQuotient.{u1} X _inst_1) Type.{u1} (DiscreteQuotient.hasCoeToSort.{u1} X _inst_1) Q) (DiscreteQuotient.proj.{u1} X _inst_1 Q x) (Qs Q)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_4 : CompactSpace.{u1} X _inst_1] (Qs : forall (Q : DiscreteQuotient.{u1} X _inst_1), Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 Q)), (forall (A : DiscreteQuotient.{u1} X _inst_1) (B : DiscreteQuotient.{u1} X _inst_1) (h : LE.le.{u1} (DiscreteQuotient.{u1} X _inst_1) (Preorder.toLE.{u1} (DiscreteQuotient.{u1} X _inst_1) (PartialOrder.toPreorder.{u1} (DiscreteQuotient.{u1} X _inst_1) (SemilatticeInf.toPartialOrder.{u1} (DiscreteQuotient.{u1} X _inst_1) (DiscreteQuotient.instSemilatticeInfDiscreteQuotient.{u1} X _inst_1)))) A B), Eq.{succ u1} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 B)) (DiscreteQuotient.ofLe.{u1} X _inst_1 A B h (Qs A)) (Qs B)) -> (Exists.{succ u1} X (fun (x : X) => forall (Q : DiscreteQuotient.{u1} X _inst_1), Eq.{succ u1} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 Q)) (DiscreteQuotient.proj.{u1} X _inst_1 Q x) (Qs Q)))
Case conversion may be inaccurate. Consider using '#align discrete_quotient.exists_of_compat DiscreteQuotient.exists_of_compatₓ'. -/
theorem exists_of_compat [CompactSpace X] (Qs : ∀ Q : DiscreteQuotient X, Q)
    (compat : ∀ (A B : DiscreteQuotient X) (h : A ≤ B), ofLe h (Qs _) = Qs _) :
    ∃ x : X, ∀ Q : DiscreteQuotient X, Q.proj x = Qs _ :=
  by
  obtain ⟨x, hx⟩ : (⋂ Q, proj Q ⁻¹' {Qs Q}).Nonempty :=
    IsCompact.nonempty_interᵢ_of_directed_nonempty_compact_closed
      (fun Q : DiscreteQuotient X => Q.proj ⁻¹' {Qs _}) (directed_of_inf fun A B h => _)
      (fun Q => (singleton_nonempty _).Preimage Q.proj_surjective)
      (fun i => (is_closed_preimage _ _).IsCompact) fun i => is_closed_preimage _ _
  · refine' ⟨x, fun Q => _⟩
    exact hx _ ⟨Q, rfl⟩
  · rw [← compat _ _ h]
    exact fiber_subset_of_le _ _
#align discrete_quotient.exists_of_compat DiscreteQuotient.exists_of_compat

instance [CompactSpace X] : Finite S :=
  by
  have : CompactSpace S := Quotient.compactSpace
  rwa [← isCompact_univ_iff, isCompact_iff_finite, finite_univ_iff] at this

end DiscreteQuotient

namespace LocallyConstant

variable {X} (f : LocallyConstant X α)

#print LocallyConstant.discreteQuotient /-
/-- Any locally constant function induces a discrete quotient. -/
def discreteQuotient : DiscreteQuotient X
    where
  toSetoid := Setoid.comap f ⊥
  isOpen_setOf_rel x := f.IsLocallyConstant _
#align locally_constant.discrete_quotient LocallyConstant.discreteQuotient
-/

#print LocallyConstant.lift /-
/-- The (locally constant) function from the discrete quotient associated to a locally constant
function. -/
def lift : LocallyConstant f.DiscreteQuotient α :=
  ⟨fun a => Quotient.liftOn' a f fun a b => id, fun A => isOpen_discrete _⟩
#align locally_constant.lift LocallyConstant.lift
-/

/- warning: locally_constant.lift_comp_proj -> LocallyConstant.lift_comp_proj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] (f : LocallyConstant.{u2, u1} X α _inst_1), Eq.{max (succ u2) (succ u1)} (X -> α) (Function.comp.{succ u2, succ u2, succ u1} X (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} X _inst_1) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} X _inst_1) (LocallyConstant.discreteQuotient.{u1, u2} α X _inst_1 f)) α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocallyConstant.{u2, u1} (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} X _inst_1) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} X _inst_1) (LocallyConstant.discreteQuotient.{u1, u2} α X _inst_1 f)) α (DiscreteQuotient.topologicalSpace.{u2} X _inst_1 (LocallyConstant.discreteQuotient.{u1, u2} α X _inst_1 f))) (fun (_x : LocallyConstant.{u2, u1} (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} X _inst_1) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} X _inst_1) (LocallyConstant.discreteQuotient.{u1, u2} α X _inst_1 f)) α (DiscreteQuotient.topologicalSpace.{u2} X _inst_1 (LocallyConstant.discreteQuotient.{u1, u2} α X _inst_1 f))) => (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} X _inst_1) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} X _inst_1) (LocallyConstant.discreteQuotient.{u1, u2} α X _inst_1 f)) -> α) (LocallyConstant.hasCoeToFun.{u2, u1} (coeSort.{succ u2, succ (succ u2)} (DiscreteQuotient.{u2} X _inst_1) Type.{u2} (DiscreteQuotient.hasCoeToSort.{u2} X _inst_1) (LocallyConstant.discreteQuotient.{u1, u2} α X _inst_1 f)) α (DiscreteQuotient.topologicalSpace.{u2} X _inst_1 (LocallyConstant.discreteQuotient.{u1, u2} α X _inst_1 f))) (LocallyConstant.lift.{u1, u2} α X _inst_1 f)) (DiscreteQuotient.proj.{u2} X _inst_1 (LocallyConstant.discreteQuotient.{u1, u2} α X _inst_1 f))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (LocallyConstant.{u2, u1} X α _inst_1) (fun (_x : LocallyConstant.{u2, u1} X α _inst_1) => X -> α) (LocallyConstant.hasCoeToFun.{u2, u1} X α _inst_1) f)
but is expected to have type
  forall {α : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (f : LocallyConstant.{u1, u2} X α _inst_1), Eq.{max (succ u2) (succ u1)} (X -> α) (Function.comp.{succ u1, succ u1, succ u2} X (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 (LocallyConstant.discreteQuotient.{u2, u1} α X _inst_1 f))) α (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (LocallyConstant.{u1, u2} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 (LocallyConstant.discreteQuotient.{u2, u1} α X _inst_1 f))) α (DiscreteQuotient.instTopologicalSpaceQuotientToSetoid.{u1} X _inst_1 (LocallyConstant.discreteQuotient.{u2, u1} α X _inst_1 f))) (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 (LocallyConstant.discreteQuotient.{u2, u1} α X _inst_1 f))) (fun (_x : Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 (LocallyConstant.discreteQuotient.{u2, u1} α X _inst_1 f))) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 (LocallyConstant.discreteQuotient.{u2, u1} α X _inst_1 f))) => α) _x) (LocallyConstant.instFunLikeLocallyConstant.{u1, u2} (Quotient.{succ u1} X (DiscreteQuotient.toSetoid.{u1} X _inst_1 (LocallyConstant.discreteQuotient.{u2, u1} α X _inst_1 f))) α (DiscreteQuotient.instTopologicalSpaceQuotientToSetoid.{u1} X _inst_1 (LocallyConstant.discreteQuotient.{u2, u1} α X _inst_1 f))) (LocallyConstant.lift.{u2, u1} α X _inst_1 f)) (DiscreteQuotient.proj.{u1} X _inst_1 (LocallyConstant.discreteQuotient.{u2, u1} α X _inst_1 f))) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (LocallyConstant.{u1, u2} X α _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => α) _x) (LocallyConstant.instFunLikeLocallyConstant.{u1, u2} X α _inst_1) f)
Case conversion may be inaccurate. Consider using '#align locally_constant.lift_comp_proj LocallyConstant.lift_comp_projₓ'. -/
@[simp]
theorem lift_comp_proj : f.lift ∘ f.DiscreteQuotient.proj = f :=
  by
  ext
  rfl
#align locally_constant.lift_comp_proj LocallyConstant.lift_comp_proj

end LocallyConstant

