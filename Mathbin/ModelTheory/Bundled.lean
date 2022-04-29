/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.ModelTheory.ElementaryMaps
import Mathbin.CategoryTheory.ConcreteCategory.Bundled

/-!
# Bundled First-Order Structures
This file bundles types together with their first-order structure.

## Main Definitions
* `first_order.language.Theory.Model` is the type of nonempty models of a particular theory.
* `first_order.language.equiv_setoid` is the isomorphism equivalence relation on bundled structures.

## TODO
* Define category structures on bundled structures and models.

-/


universe u v w w'

variable {L : FirstOrder.Language.{u, v}}

@[protected]
instance CategoryTheory.Bundled.structure {L : FirstOrder.Language.{u, v}}
    (M : CategoryTheory.Bundled.{w} L.Structure) : L.Structure M :=
  M.str

namespace FirstOrder

namespace Language

open FirstOrder

/-- The equivalence relation on bundled `L.Structure`s indicating that they are isomorphic. -/
instance equivSetoid : Setoidₓ (CategoryTheory.Bundled L.Structure) where
  R := fun M N => Nonempty (M ≃[L] N)
  iseqv :=
    ⟨fun M => ⟨Equiv.refl L M⟩, fun M N => Nonempty.map Equiv.symm, fun M N P => Nonempty.map2 fun MN NP => NP.comp MN⟩

variable (T : L.Theory)

namespace Theory

/-- The type of nonempty models of a first-order theory. -/
structure ModelCat where
  Carrier : Type w
  [struc : L.Structure carrier]
  [is_model : T.Model carrier]
  [nonempty' : Nonempty carrier]

attribute [instance] Model.struc Model.is_model Model.nonempty'

namespace Model

instance : CoeSort T.Model (Type w) :=
  ⟨ModelCat.Carrier⟩

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. -/
def of (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M] : T.Model :=
  ⟨M⟩

@[simp]
theorem coe_of (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M] : (of T M : Type w) = M :=
  rfl

instance (M : T.Model) : Nonempty M :=
  inferInstance

section Inhabited

attribute [local instance] trivial_unit_structure

instance : Inhabited (ModelCat (∅ : L.Theory)) :=
  ⟨ModelCat.of _ Unit⟩

end Inhabited

variable {T}

/-- Maps a bundled model along a bijection. -/
def equivInduced {M : ModelCat.{u, v, w} T} {N : Type w'} (e : M ≃ N) : ModelCat.{u, v, w'} T where
  Carrier := N
  struc := e.inducedStructure
  is_model := @Equiv.Theory_model L M N _ e.inducedStructure T e.inducedStructureEquiv _
  nonempty' := e.symm.Nonempty

/-- Shrinks a small model to a particular universe. -/
noncomputable def shrink (M : ModelCat.{u, v, w} T) [Small.{w'} M] : ModelCat.{u, v, w'} T :=
  equivInduced (equivShrink M)

/-- Lifts a model to a particular universe. -/
def ulift (M : ModelCat.{u, v, w} T) : ModelCat.{u, v, max w w'} T :=
  equivInduced (Equivₓ.ulift.symm : M ≃ _)

end Model

variable {T}

/-- Bundles `M ⊨ T` as a `T.Model`. -/
def Model.bundled {M : Type w} [LM : L.Structure M] [ne : Nonempty M] (h : M ⊨ T) : T.Model :=
  @ModelCat.of L T M LM h Ne

@[simp]
theorem coe_of {M : Type w} [L.Structure M] [Nonempty M] (h : M ⊨ T) : (h.Bundled : Type w) = M :=
  rfl

end Theory

/-- An elementary substructure of a bundled model as a bundled model. -/
def ElementarySubstructure.toModel {M : T.Model} (S : L.ElementarySubstructure M) : T.Model :=
  Theory.ModelCat.of T S

instance {M : T.Model} (S : L.ElementarySubstructure M) [h : Small S] : Small (S.toModel T) :=
  h

end Language

end FirstOrder

