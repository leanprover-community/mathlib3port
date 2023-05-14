/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module model_theory.definability
! leanprover-community/mathlib commit 6cf5900728239efa287df7761ec2a1ac9cf39b29
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.SetLike.Basic
import Mathbin.ModelTheory.Semantics

/-!
# Definable Sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file defines what it means for a set over a first-order structure to be definable.

## Main Definitions
* `set.definable` is defined so that `A.definable L s` indicates that the
set `s` of a finite cartesian power of `M` is definable with parameters in `A`.
* `set.definable₁` is defined so that `A.definable₁ L s` indicates that
`(s : set M)` is definable with parameters in `A`.
* `set.definable₂` is defined so that `A.definable₂ L s` indicates that
`(s : set (M × M))` is definable with parameters in `A`.
* A `first_order.language.definable_set` is defined so that `L.definable_set A α` is the boolean
  algebra of subsets of `α → M` defined by formulas with parameters in `A`.

## Main Results
* `L.definable_set A α` forms a `boolean_algebra`
* `set.definable.image_comp` shows that definability is closed under projections in finite
  dimensions.

-/


universe u v w

namespace Set

variable {M : Type w} (A : Set M) (L : FirstOrder.Language.{u, v}) [L.Structure M]

open FirstOrder

open FirstOrder.Language FirstOrder.Language.Structure

variable {α : Type _} {β : Type _}

#print Set.Definable /-
/-- A subset of a finite Cartesian product of a structure is definable over a set `A` when
  membership in the set is given by a first-order formula with parameters from `A`. -/
def Definable (s : Set (α → M)) : Prop :=
  ∃ φ : L[[A]].Formula α, s = setOf φ.realize
#align set.definable Set.Definable
-/

variable {L} {A} {B : Set M} {s : Set (α → M)}

/- warning: set.definable.map_expansion -> Set.Definable.map_expansion is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {s : Set.{max u4 u3} (α -> M)} {L' : FirstOrder.Language.{u5, u6}} [_inst_2 : FirstOrder.Language.Structure.{u5, u6, u3} L' M], (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α s) -> (forall (φ : FirstOrder.Language.LHom.{u1, u2, u5, u6} L L') [_inst_3 : FirstOrder.Language.LHom.IsExpansionOn.{u1, u2, u5, u6, u3} L L' φ M _inst_1 _inst_2], Set.Definable.{u5, u6, u3, u4} M A L' _inst_2 α s)
but is expected to have type
  forall {M : Type.{u5}} {A : Set.{u5} M} {L : FirstOrder.Language.{u3, u4}} [_inst_1 : FirstOrder.Language.Structure.{u3, u4, u5} L M] {α : Type.{u6}} {s : Set.{max u6 u5} (α -> M)} {L' : FirstOrder.Language.{u2, u1}} [_inst_2 : FirstOrder.Language.Structure.{u2, u1, u5} L' M], (Set.Definable.{u3, u4, u5, u6} M A L _inst_1 α s) -> (forall (φ : FirstOrder.Language.LHom.{u3, u4, u2, u1} L L') [_inst_3 : FirstOrder.Language.LHom.IsExpansionOn.{u3, u4, u2, u1, u5} L L' φ M _inst_1 _inst_2], Set.Definable.{u2, u1, u5, u6} M A L' _inst_2 α s)
Case conversion may be inaccurate. Consider using '#align set.definable.map_expansion Set.Definable.map_expansionₓ'. -/
theorem Definable.map_expansion {L' : FirstOrder.Language} [L'.Structure M] (h : A.Definable L s)
    (φ : L →ᴸ L') [φ.IsExpansionOn M] : A.Definable L' s :=
  by
  obtain ⟨ψ, rfl⟩ := h
  refine' ⟨(φ.add_constants A).onFormula ψ, _⟩
  ext x
  simp only [mem_set_of_eq, Lhom.realize_on_formula]
#align set.definable.map_expansion Set.Definable.map_expansion

#print Set.empty_definable_iff /-
theorem empty_definable_iff : (∅ : Set M).Definable L s ↔ ∃ φ : L.Formula α, s = setOf φ.realize :=
  by
  rw [definable, Equiv.exists_congr_left (Lequiv.add_empty_constants L (∅ : Set M)).onFormula]
  simp
#align set.empty_definable_iff Set.empty_definable_iff
-/

#print Set.definable_iff_empty_definable_with_params /-
theorem definable_iff_empty_definable_with_params :
    A.Definable L s ↔ (∅ : Set M).Definable (L[[A]]) s :=
  empty_definable_iff.symm
#align set.definable_iff_empty_definable_with_params Set.definable_iff_empty_definable_with_params
-/

#print Set.Definable.mono /-
theorem Definable.mono (hAs : A.Definable L s) (hAB : A ⊆ B) : B.Definable L s :=
  by
  rw [definable_iff_empty_definable_with_params] at *
  exact hAs.map_expansion (L.Lhom_with_constants_map (Set.inclusion hAB))
#align set.definable.mono Set.Definable.mono
-/

#print Set.definable_empty /-
@[simp]
theorem definable_empty : A.Definable L (∅ : Set (α → M)) :=
  ⟨⊥, by
    ext
    simp⟩
#align set.definable_empty Set.definable_empty
-/

#print Set.definable_univ /-
@[simp]
theorem definable_univ : A.Definable L (univ : Set (α → M)) :=
  ⟨⊤, by
    ext
    simp⟩
#align set.definable_univ Set.definable_univ
-/

/- warning: set.definable.inter -> Set.Definable.inter is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {f : Set.{max u4 u3} (α -> M)} {g : Set.{max u4 u3} (α -> M)}, (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α f) -> (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α g) -> (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (Inter.inter.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.hasInter.{max u4 u3} (α -> M)) f g))
but is expected to have type
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {f : Set.{max u4 u3} (α -> M)} {g : Set.{max u4 u3} (α -> M)}, (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α f) -> (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α g) -> (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (Inter.inter.{max u3 u4} (Set.{max u4 u3} (α -> M)) (Set.instInterSet.{max u4 u3} (α -> M)) f g))
Case conversion may be inaccurate. Consider using '#align set.definable.inter Set.Definable.interₓ'. -/
@[simp]
theorem Definable.inter {f g : Set (α → M)} (hf : A.Definable L f) (hg : A.Definable L g) :
    A.Definable L (f ∩ g) := by
  rcases hf with ⟨φ, rfl⟩
  rcases hg with ⟨θ, rfl⟩
  refine' ⟨φ ⊓ θ, _⟩
  ext
  simp
#align set.definable.inter Set.Definable.inter

/- warning: set.definable.union -> Set.Definable.union is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {f : Set.{max u4 u3} (α -> M)} {g : Set.{max u4 u3} (α -> M)}, (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α f) -> (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α g) -> (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (Union.union.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.hasUnion.{max u4 u3} (α -> M)) f g))
but is expected to have type
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {f : Set.{max u4 u3} (α -> M)} {g : Set.{max u4 u3} (α -> M)}, (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α f) -> (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α g) -> (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (Union.union.{max u3 u4} (Set.{max u4 u3} (α -> M)) (Set.instUnionSet.{max u4 u3} (α -> M)) f g))
Case conversion may be inaccurate. Consider using '#align set.definable.union Set.Definable.unionₓ'. -/
@[simp]
theorem Definable.union {f g : Set (α → M)} (hf : A.Definable L f) (hg : A.Definable L g) :
    A.Definable L (f ∪ g) := by
  rcases hf with ⟨φ, hφ⟩
  rcases hg with ⟨θ, hθ⟩
  refine' ⟨φ ⊔ θ, _⟩
  ext
  rw [hφ, hθ, mem_set_of_eq, formula.realize_sup, mem_union, mem_set_of_eq, mem_set_of_eq]
#align set.definable.union Set.Definable.union

/- warning: set.definable_finset_inf -> Set.definable_finset_inf is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {ι : Type.{u5}} {f : ι -> (Set.{max u4 u3} (α -> M))}, (forall (i : ι), Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (f i)) -> (forall (s : Finset.{u5} ι), Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (Finset.inf.{max u4 u3, u5} (Set.{max u4 u3} (α -> M)) ι (Lattice.toSemilatticeInf.{max u4 u3} (Set.{max u4 u3} (α -> M)) (ConditionallyCompleteLattice.toLattice.{max u4 u3} (Set.{max u4 u3} (α -> M)) (CompleteLattice.toConditionallyCompleteLattice.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Order.Coframe.toCompleteLattice.{max u4 u3} (Set.{max u4 u3} (α -> M)) (CompleteDistribLattice.toCoframe.{max u4 u3} (Set.{max u4 u3} (α -> M)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.completeBooleanAlgebra.{max u4 u3} (α -> M)))))))) (Set.orderTop.{max u4 u3} (α -> M)) s f))
but is expected to have type
  forall {M : Type.{u4}} {A : Set.{u4} M} {L : FirstOrder.Language.{u2, u3}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] {α : Type.{u5}} {ι : Type.{u1}} {f : ι -> (Set.{max u5 u4} (α -> M))}, (forall (i : ι), Set.Definable.{u2, u3, u4, u5} M A L _inst_1 α (f i)) -> (forall (s : Finset.{u1} ι), Set.Definable.{u2, u3, u4, u5} M A L _inst_1 α (Finset.inf.{max u4 u5, u1} (Set.{max u5 u4} (α -> M)) ι (Lattice.toSemilatticeInf.{max u5 u4} (Set.{max u5 u4} (α -> M)) (ConditionallyCompleteLattice.toLattice.{max u5 u4} (Set.{max u5 u4} (α -> M)) (CompleteLattice.toConditionallyCompleteLattice.{max u5 u4} (Set.{max u5 u4} (α -> M)) (Order.Coframe.toCompleteLattice.{max u5 u4} (Set.{max u5 u4} (α -> M)) (CompleteDistribLattice.toCoframe.{max u5 u4} (Set.{max u5 u4} (α -> M)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{max u5 u4} (Set.{max u5 u4} (α -> M)) (Set.instCompleteBooleanAlgebraSet.{max u5 u4} (α -> M)))))))) (Set.instOrderTopSetInstLESet.{max u5 u4} (α -> M)) s f))
Case conversion may be inaccurate. Consider using '#align set.definable_finset_inf Set.definable_finset_infₓ'. -/
theorem definable_finset_inf {ι : Type _} {f : ∀ i : ι, Set (α → M)} (hf : ∀ i, A.Definable L (f i))
    (s : Finset ι) : A.Definable L (s.inf f) := by
  classical
    refine' Finset.induction definable_univ (fun i s is h => _) s
    rw [Finset.inf_insert]
    exact (hf i).inter h
#align set.definable_finset_inf Set.definable_finset_inf

/- warning: set.definable_finset_sup -> Set.definable_finset_sup is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {ι : Type.{u5}} {f : ι -> (Set.{max u4 u3} (α -> M))}, (forall (i : ι), Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (f i)) -> (forall (s : Finset.{u5} ι), Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (Finset.sup.{max u4 u3, u5} (Set.{max u4 u3} (α -> M)) ι (Lattice.toSemilatticeSup.{max u4 u3} (Set.{max u4 u3} (α -> M)) (ConditionallyCompleteLattice.toLattice.{max u4 u3} (Set.{max u4 u3} (α -> M)) (CompleteLattice.toConditionallyCompleteLattice.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Order.Coframe.toCompleteLattice.{max u4 u3} (Set.{max u4 u3} (α -> M)) (CompleteDistribLattice.toCoframe.{max u4 u3} (Set.{max u4 u3} (α -> M)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.completeBooleanAlgebra.{max u4 u3} (α -> M)))))))) (GeneralizedBooleanAlgebra.toOrderBot.{max u4 u3} (Set.{max u4 u3} (α -> M)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.booleanAlgebra.{max u4 u3} (α -> M)))) s f))
but is expected to have type
  forall {M : Type.{u4}} {A : Set.{u4} M} {L : FirstOrder.Language.{u2, u3}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] {α : Type.{u5}} {ι : Type.{u1}} {f : ι -> (Set.{max u5 u4} (α -> M))}, (forall (i : ι), Set.Definable.{u2, u3, u4, u5} M A L _inst_1 α (f i)) -> (forall (s : Finset.{u1} ι), Set.Definable.{u2, u3, u4, u5} M A L _inst_1 α (Finset.sup.{max u4 u5, u1} (Set.{max u5 u4} (α -> M)) ι (Lattice.toSemilatticeSup.{max u5 u4} (Set.{max u5 u4} (α -> M)) (ConditionallyCompleteLattice.toLattice.{max u5 u4} (Set.{max u5 u4} (α -> M)) (CompleteLattice.toConditionallyCompleteLattice.{max u5 u4} (Set.{max u5 u4} (α -> M)) (Order.Coframe.toCompleteLattice.{max u5 u4} (Set.{max u5 u4} (α -> M)) (CompleteDistribLattice.toCoframe.{max u5 u4} (Set.{max u5 u4} (α -> M)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{max u5 u4} (Set.{max u5 u4} (α -> M)) (Set.instCompleteBooleanAlgebraSet.{max u5 u4} (α -> M)))))))) (BoundedOrder.toOrderBot.{max u5 u4} (Set.{max u5 u4} (α -> M)) (Preorder.toLE.{max u4 u5} (Set.{max u5 u4} (α -> M)) (PartialOrder.toPreorder.{max u4 u5} (Set.{max u5 u4} (α -> M)) (SemilatticeSup.toPartialOrder.{max u4 u5} (Set.{max u5 u4} (α -> M)) (Lattice.toSemilatticeSup.{max u5 u4} (Set.{max u5 u4} (α -> M)) (ConditionallyCompleteLattice.toLattice.{max u5 u4} (Set.{max u5 u4} (α -> M)) (CompleteLattice.toConditionallyCompleteLattice.{max u5 u4} (Set.{max u5 u4} (α -> M)) (Order.Coframe.toCompleteLattice.{max u5 u4} (Set.{max u5 u4} (α -> M)) (CompleteDistribLattice.toCoframe.{max u5 u4} (Set.{max u5 u4} (α -> M)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{max u5 u4} (Set.{max u5 u4} (α -> M)) (Set.instCompleteBooleanAlgebraSet.{max u5 u4} (α -> M))))))))))) (CompleteLattice.toBoundedOrder.{max u5 u4} (Set.{max u5 u4} (α -> M)) (Order.Coframe.toCompleteLattice.{max u5 u4} (Set.{max u5 u4} (α -> M)) (CompleteDistribLattice.toCoframe.{max u5 u4} (Set.{max u5 u4} (α -> M)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{max u5 u4} (Set.{max u5 u4} (α -> M)) (Set.instCompleteBooleanAlgebraSet.{max u5 u4} (α -> M))))))) s f))
Case conversion may be inaccurate. Consider using '#align set.definable_finset_sup Set.definable_finset_supₓ'. -/
theorem definable_finset_sup {ι : Type _} {f : ∀ i : ι, Set (α → M)} (hf : ∀ i, A.Definable L (f i))
    (s : Finset ι) : A.Definable L (s.sup f) := by
  classical
    refine' Finset.induction definable_empty (fun i s is h => _) s
    rw [Finset.sup_insert]
    exact (hf i).union h
#align set.definable_finset_sup Set.definable_finset_sup

/- warning: set.definable_finset_bInter -> Set.definable_finset_binterᵢ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {ι : Type.{u5}} {f : ι -> (Set.{max u4 u3} (α -> M))}, (forall (i : ι), Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (f i)) -> (forall (s : Finset.{u5} ι), Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (Set.interᵢ.{max u4 u3, succ u5} (α -> M) ι (fun (i : ι) => Set.interᵢ.{max u4 u3, 0} (α -> M) (Membership.Mem.{u5, u5} ι (Finset.{u5} ι) (Finset.hasMem.{u5} ι) i s) (fun (H : Membership.Mem.{u5, u5} ι (Finset.{u5} ι) (Finset.hasMem.{u5} ι) i s) => f i))))
but is expected to have type
  forall {M : Type.{u4}} {A : Set.{u4} M} {L : FirstOrder.Language.{u2, u3}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] {α : Type.{u5}} {ι : Type.{u1}} {f : ι -> (Set.{max u5 u4} (α -> M))}, (forall (i : ι), Set.Definable.{u2, u3, u4, u5} M A L _inst_1 α (f i)) -> (forall (s : Finset.{u1} ι), Set.Definable.{u2, u3, u4, u5} M A L _inst_1 α (Set.interᵢ.{max u4 u5, succ u1} (α -> M) ι (fun (i : ι) => Set.interᵢ.{max u4 u5, 0} (α -> M) (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (fun (H : Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) => f i))))
Case conversion may be inaccurate. Consider using '#align set.definable_finset_bInter Set.definable_finset_binterᵢₓ'. -/
theorem definable_finset_binterᵢ {ι : Type _} {f : ∀ i : ι, Set (α → M)}
    (hf : ∀ i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (⋂ i ∈ s, f i) :=
  by
  rw [← Finset.inf_set_eq_interᵢ]
  exact definable_finset_inf hf s
#align set.definable_finset_bInter Set.definable_finset_binterᵢ

/- warning: set.definable_finset_bUnion -> Set.definable_finset_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {ι : Type.{u5}} {f : ι -> (Set.{max u4 u3} (α -> M))}, (forall (i : ι), Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (f i)) -> (forall (s : Finset.{u5} ι), Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (Set.unionᵢ.{max u4 u3, succ u5} (α -> M) ι (fun (i : ι) => Set.unionᵢ.{max u4 u3, 0} (α -> M) (Membership.Mem.{u5, u5} ι (Finset.{u5} ι) (Finset.hasMem.{u5} ι) i s) (fun (H : Membership.Mem.{u5, u5} ι (Finset.{u5} ι) (Finset.hasMem.{u5} ι) i s) => f i))))
but is expected to have type
  forall {M : Type.{u4}} {A : Set.{u4} M} {L : FirstOrder.Language.{u2, u3}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] {α : Type.{u5}} {ι : Type.{u1}} {f : ι -> (Set.{max u5 u4} (α -> M))}, (forall (i : ι), Set.Definable.{u2, u3, u4, u5} M A L _inst_1 α (f i)) -> (forall (s : Finset.{u1} ι), Set.Definable.{u2, u3, u4, u5} M A L _inst_1 α (Set.unionᵢ.{max u4 u5, succ u1} (α -> M) ι (fun (i : ι) => Set.unionᵢ.{max u4 u5, 0} (α -> M) (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (fun (H : Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) => f i))))
Case conversion may be inaccurate. Consider using '#align set.definable_finset_bUnion Set.definable_finset_bunionᵢₓ'. -/
theorem definable_finset_bunionᵢ {ι : Type _} {f : ∀ i : ι, Set (α → M)}
    (hf : ∀ i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (⋃ i ∈ s, f i) :=
  by
  rw [← Finset.sup_set_eq_bunionᵢ]
  exact definable_finset_sup hf s
#align set.definable_finset_bUnion Set.definable_finset_bunionᵢ

/- warning: set.definable.compl -> Set.Definable.compl is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {s : Set.{max u4 u3} (α -> M)}, (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α s) -> (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (HasCompl.compl.{max u4 u3} (Set.{max u4 u3} (α -> M)) (BooleanAlgebra.toHasCompl.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.booleanAlgebra.{max u4 u3} (α -> M))) s))
but is expected to have type
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {s : Set.{max u4 u3} (α -> M)}, (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α s) -> (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (HasCompl.compl.{max u3 u4} (Set.{max u4 u3} (α -> M)) (BooleanAlgebra.toHasCompl.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.instBooleanAlgebraSet.{max u4 u3} (α -> M))) s))
Case conversion may be inaccurate. Consider using '#align set.definable.compl Set.Definable.complₓ'. -/
@[simp]
theorem Definable.compl {s : Set (α → M)} (hf : A.Definable L s) : A.Definable L (sᶜ) :=
  by
  rcases hf with ⟨φ, hφ⟩
  refine' ⟨φ.not, _⟩
  rw [hφ]
  rfl
#align set.definable.compl Set.Definable.compl

/- warning: set.definable.sdiff -> Set.Definable.sdiff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {s : Set.{max u4 u3} (α -> M)} {t : Set.{max u4 u3} (α -> M)}, (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α s) -> (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α t) -> (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (SDiff.sdiff.{max u4 u3} (Set.{max u4 u3} (α -> M)) (BooleanAlgebra.toHasSdiff.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.booleanAlgebra.{max u4 u3} (α -> M))) s t))
but is expected to have type
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {s : Set.{max u4 u3} (α -> M)} {t : Set.{max u4 u3} (α -> M)}, (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α s) -> (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α t) -> (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (SDiff.sdiff.{max u3 u4} (Set.{max u4 u3} (α -> M)) (Set.instSDiffSet.{max u4 u3} (α -> M)) s t))
Case conversion may be inaccurate. Consider using '#align set.definable.sdiff Set.Definable.sdiffₓ'. -/
@[simp]
theorem Definable.sdiff {s t : Set (α → M)} (hs : A.Definable L s) (ht : A.Definable L t) :
    A.Definable L (s \ t) :=
  hs.inter ht.compl
#align set.definable.sdiff Set.Definable.sdiff

/- warning: set.definable.preimage_comp -> Set.Definable.preimage_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {β : Type.{u5}} (f : α -> β) {s : Set.{max u4 u3} (α -> M)}, (Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α s) -> (Set.Definable.{u1, u2, u3, u5} M A L _inst_1 β (Set.preimage.{max u5 u3, max u4 u3} (β -> M) (α -> M) (fun (g : β -> M) => Function.comp.{succ u4, succ u5, succ u3} α β M g f) s))
but is expected to have type
  forall {M : Type.{u4}} {A : Set.{u4} M} {L : FirstOrder.Language.{u2, u3}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] {α : Type.{u5}} {β : Type.{u1}} (f : α -> β) {s : Set.{max u5 u4} (α -> M)}, (Set.Definable.{u2, u3, u4, u5} M A L _inst_1 α s) -> (Set.Definable.{u2, u3, u4, u1} M A L _inst_1 β (Set.preimage.{max u4 u1, max u5 u4} (β -> M) (α -> M) (fun (g : β -> M) => Function.comp.{succ u5, succ u1, succ u4} α β M g f) s))
Case conversion may be inaccurate. Consider using '#align set.definable.preimage_comp Set.Definable.preimage_compₓ'. -/
theorem Definable.preimage_comp (f : α → β) {s : Set (α → M)} (h : A.Definable L s) :
    A.Definable L ((fun g : β → M => g ∘ f) ⁻¹' s) :=
  by
  obtain ⟨φ, rfl⟩ := h
  refine' ⟨φ.relabel f, _⟩
  ext
  simp only [Set.preimage_setOf_eq, mem_set_of_eq, formula.realize_relabel]
#align set.definable.preimage_comp Set.Definable.preimage_comp

/- warning: set.definable.image_comp_equiv -> Set.Definable.image_comp_equiv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {β : Type.{u5}} {s : Set.{max u5 u3} (β -> M)}, (Set.Definable.{u1, u2, u3, u5} M A L _inst_1 β s) -> (forall (f : Equiv.{succ u4, succ u5} α β), Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (Set.image.{max u5 u3, max u4 u3} (β -> M) (α -> M) (fun (g : β -> M) => Function.comp.{succ u4, succ u5, succ u3} α β M g (coeFn.{max 1 (max (succ u4) (succ u5)) (succ u5) (succ u4), max (succ u4) (succ u5)} (Equiv.{succ u4, succ u5} α β) (fun (_x : Equiv.{succ u4, succ u5} α β) => α -> β) (Equiv.hasCoeToFun.{succ u4, succ u5} α β) f)) s))
but is expected to have type
  forall {M : Type.{u4}} {A : Set.{u4} M} {L : FirstOrder.Language.{u2, u3}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] {α : Type.{u5}} {β : Type.{u1}} {s : Set.{max u4 u1} (β -> M)}, (Set.Definable.{u2, u3, u4, u1} M A L _inst_1 β s) -> (forall (f : Equiv.{succ u5, succ u1} α β), Set.Definable.{u2, u3, u4, u5} M A L _inst_1 α (Set.image.{max u4 u1, max u4 u5} (β -> M) (α -> M) (fun (g : β -> M) => Function.comp.{succ u5, succ u1, succ u4} α β M g (FunLike.coe.{max (succ u5) (succ u1), succ u5, succ u1} (Equiv.{succ u5, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u5, succ u1} α β) f)) s))
Case conversion may be inaccurate. Consider using '#align set.definable.image_comp_equiv Set.Definable.image_comp_equivₓ'. -/
theorem Definable.image_comp_equiv {s : Set (β → M)} (h : A.Definable L s) (f : α ≃ β) :
    A.Definable L ((fun g : β → M => g ∘ f) '' s) :=
  by
  refine' (congr rfl _).mp (h.preimage_comp f.symm)
  rw [image_eq_preimage_of_inverse]
  · intro i
    ext b
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  · intro i
    ext a
    simp
#align set.definable.image_comp_equiv Set.Definable.image_comp_equiv

#print Set.Definable.image_comp_sum_inl_fin /-
/-- This lemma is only intended as a helper for `definable.image_comp. -/
theorem Definable.image_comp_sum_inl_fin (m : ℕ) {s : Set (Sum α (Fin m) → M)}
    (h : A.Definable L s) : A.Definable L ((fun g : Sum α (Fin m) → M => g ∘ Sum.inl) '' s) :=
  by
  obtain ⟨φ, rfl⟩ := h
  refine' ⟨(bounded_formula.relabel id φ).exs, _⟩
  ext x
  simp only [Set.mem_image, mem_set_of_eq, bounded_formula.realize_exs,
    bounded_formula.realize_relabel, Function.comp.right_id, Fin.castAdd_zero, Fin.cast_refl]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact
      ⟨y ∘ Sum.inr, (congr (congr rfl (Sum.elim_comp_inl_inr y).symm) (funext finZeroElim)).mp hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨Sum.elim x y, (congr rfl (funext finZeroElim)).mp hy, Sum.elim_comp_inl _ _⟩
#align set.definable.image_comp_sum_inl_fin Set.Definable.image_comp_sum_inl_fin
-/

/- warning: set.definable.image_comp_embedding -> Set.Definable.image_comp_embedding is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {β : Type.{u5}} {s : Set.{max u5 u3} (β -> M)}, (Set.Definable.{u1, u2, u3, u5} M A L _inst_1 β s) -> (forall (f : Function.Embedding.{succ u4, succ u5} α β) [_inst_2 : Finite.{succ u5} β], Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (Set.image.{max u5 u3, max u4 u3} (β -> M) (α -> M) (fun (g : β -> M) => Function.comp.{succ u4, succ u5, succ u3} α β M g (coeFn.{max 1 (succ u4) (succ u5), max (succ u4) (succ u5)} (Function.Embedding.{succ u4, succ u5} α β) (fun (_x : Function.Embedding.{succ u4, succ u5} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u4, succ u5} α β) f)) s))
but is expected to have type
  forall {M : Type.{u4}} {A : Set.{u4} M} {L : FirstOrder.Language.{u2, u3}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] {α : Type.{u5}} {β : Type.{u1}} {s : Set.{max u4 u1} (β -> M)}, (Set.Definable.{u2, u3, u4, u1} M A L _inst_1 β s) -> (forall (f : Function.Embedding.{succ u5, succ u1} α β) [_inst_2 : Finite.{succ u1} β], Set.Definable.{u2, u3, u4, u5} M A L _inst_1 α (Set.image.{max u4 u1, max u4 u5} (β -> M) (α -> M) (fun (g : β -> M) => Function.comp.{succ u5, succ u1, succ u4} α β M g (FunLike.coe.{max (succ u5) (succ u1), succ u5, succ u1} (Function.Embedding.{succ u5, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u5) (succ u1), succ u5, succ u1} (Function.Embedding.{succ u5, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u5, succ u1} α β)) f)) s))
Case conversion may be inaccurate. Consider using '#align set.definable.image_comp_embedding Set.Definable.image_comp_embeddingₓ'. -/
/-- Shows that definability is closed under finite projections. -/
theorem Definable.image_comp_embedding {s : Set (β → M)} (h : A.Definable L s) (f : α ↪ β)
    [Finite β] : A.Definable L ((fun g : β → M => g ∘ f) '' s) := by
  classical
    cases nonempty_fintype β
    refine'
      (congr rfl (ext fun x => _)).mp
        (((h.image_comp_equiv (Equiv.Set.sumCompl (range f))).image_comp_equiv
              (Equiv.sumCongr (Equiv.ofInjective f f.injective)
                (Fintype.equivFin _).symm)).image_comp_sum_inl_fin
          _)
    simp only [mem_preimage, mem_image, exists_exists_and_eq_and]
    refine' exists_congr fun y => and_congr_right fun ys => Eq.congr_left (funext fun a => _)
    simp
#align set.definable.image_comp_embedding Set.Definable.image_comp_embedding

/- warning: set.definable.image_comp -> Set.Definable.image_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u3}} {A : Set.{u3} M} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {β : Type.{u5}} {s : Set.{max u5 u3} (β -> M)}, (Set.Definable.{u1, u2, u3, u5} M A L _inst_1 β s) -> (forall (f : α -> β) [_inst_2 : Finite.{succ u4} α] [_inst_3 : Finite.{succ u5} β], Set.Definable.{u1, u2, u3, u4} M A L _inst_1 α (Set.image.{max u5 u3, max u4 u3} (β -> M) (α -> M) (fun (g : β -> M) => Function.comp.{succ u4, succ u5, succ u3} α β M g f) s))
but is expected to have type
  forall {M : Type.{u4}} {A : Set.{u4} M} {L : FirstOrder.Language.{u2, u3}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] {α : Type.{u5}} {β : Type.{u1}} {s : Set.{max u4 u1} (β -> M)}, (Set.Definable.{u2, u3, u4, u1} M A L _inst_1 β s) -> (forall (f : α -> β) [_inst_2 : Finite.{succ u5} α] [_inst_3 : Finite.{succ u1} β], Set.Definable.{u2, u3, u4, u5} M A L _inst_1 α (Set.image.{max u4 u1, max u4 u5} (β -> M) (α -> M) (fun (g : β -> M) => Function.comp.{succ u5, succ u1, succ u4} α β M g f) s))
Case conversion may be inaccurate. Consider using '#align set.definable.image_comp Set.Definable.image_compₓ'. -/
/-- Shows that definability is closed under finite projections. -/
theorem Definable.image_comp {s : Set (β → M)} (h : A.Definable L s) (f : α → β) [Finite α]
    [Finite β] : A.Definable L ((fun g : β → M => g ∘ f) '' s) := by
  classical
    cases nonempty_fintype α
    cases nonempty_fintype β
    have h :=
      (((h.image_comp_equiv (Equiv.Set.sumCompl (range f))).image_comp_equiv
                (Equiv.sumCongr (_root_.equiv.refl _)
                  (Fintype.equivFin _).symm)).image_comp_sum_inl_fin
            _).preimage_comp
        (range_splitting f)
    have h' :
      A.definable L { x : α → M | ∀ a, x a = x (range_splitting f (range_factorization f a)) } :=
      by
      have h' :
        ∀ a, A.definable L { x : α → M | x a = x (range_splitting f (range_factorization f a)) } :=
        by
        refine' fun a => ⟨(var a).equal (var (range_splitting f (range_factorization f a))), ext _⟩
        simp
      refine' (congr rfl (ext _)).mp (definable_finset_bInter h' Finset.univ)
      simp
    refine' (congr rfl (ext fun x => _)).mp (h.inter h')
    simp only [Equiv.coe_trans, mem_inter_iff, mem_preimage, mem_image, exists_exists_and_eq_and,
      mem_set_of_eq]
    constructor
    · rintro ⟨⟨y, ys, hy⟩, hx⟩
      refine' ⟨y, ys, _⟩
      ext a
      rw [hx a, ← Function.comp_apply x, ← hy]
      simp
    · rintro ⟨y, ys, rfl⟩
      refine' ⟨⟨y, ys, _⟩, fun a => _⟩
      · ext
        simp [Set.apply_rangeSplitting f]
      ·
        rw [Function.comp_apply, Function.comp_apply, apply_range_splitting f,
          range_factorization_coe]
#align set.definable.image_comp Set.Definable.image_comp

variable (L) {M} (A)

#print Set.Definable₁ /-
/-- A 1-dimensional version of `definable`, for `set M`. -/
def Definable₁ (s : Set M) : Prop :=
  A.Definable L { x : Fin 1 → M | x 0 ∈ s }
#align set.definable₁ Set.Definable₁
-/

#print Set.Definable₂ /-
/-- A 2-dimensional version of `definable`, for `set (M × M)`. -/
def Definable₂ (s : Set (M × M)) : Prop :=
  A.Definable L { x : Fin 2 → M | (x 0, x 1) ∈ s }
#align set.definable₂ Set.Definable₂
-/

end Set

namespace FirstOrder

namespace Language

open Set

variable (L : FirstOrder.Language.{u, v}) {M : Type w} [L.Structure M] (A : Set M) (α : Type _)

#print FirstOrder.Language.DefinableSet /-
/-- Definable sets are subsets of finite Cartesian products of a structure such that membership is
  given by a first-order formula. -/
def DefinableSet :=
  { s : Set (α → M) // A.Definable L s }
#align first_order.language.definable_set FirstOrder.Language.DefinableSet
-/

namespace DefinableSet

variable {L A α} {s t : L.DefinableSet A α} {x : α → M}

instance : SetLike (L.DefinableSet A α) (α → M)
    where
  coe := Subtype.val
  coe_injective' := Subtype.val_injective

instance : Top (L.DefinableSet A α) :=
  ⟨⟨⊤, definable_univ⟩⟩

instance : Bot (L.DefinableSet A α) :=
  ⟨⟨⊥, definable_empty⟩⟩

instance : Sup (L.DefinableSet A α) :=
  ⟨fun s t => ⟨s ∪ t, s.2.union t.2⟩⟩

instance : Inf (L.DefinableSet A α) :=
  ⟨fun s t => ⟨s ∩ t, s.2.inter t.2⟩⟩

instance : HasCompl (L.DefinableSet A α) :=
  ⟨fun s => ⟨sᶜ, s.2.compl⟩⟩

instance : SDiff (L.DefinableSet A α) :=
  ⟨fun s t => ⟨s \ t, s.2.sdiff t.2⟩⟩

instance : Inhabited (L.DefinableSet A α) :=
  ⟨⊥⟩

/- warning: first_order.language.definable_set.le_iff -> FirstOrder.Language.DefinableSet.le_iff is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {A : Set.{u3} M} {α : Type.{u4}} {s : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α} {t : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α}, Iff (LE.le.{max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Preorder.toLE.{max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (PartialOrder.toPreorder.{max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (SetLike.partialOrder.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α)))) s t) (LE.le.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.hasLe.{max u4 u3} (α -> M)) ((fun (a : Type.{max u4 u3}) (b : Type.{max u4 u3}) [self : HasLiftT.{succ (max u4 u3), succ (max u4 u3)} a b] => self.0) (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (HasLiftT.mk.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (CoeTCₓ.coe.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (SetLike.Set.hasCoeT.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α)))) s) ((fun (a : Type.{max u4 u3}) (b : Type.{max u4 u3}) [self : HasLiftT.{succ (max u4 u3), succ (max u4 u3)} a b] => self.0) (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (HasLiftT.mk.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (CoeTCₓ.coe.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (SetLike.Set.hasCoeT.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α)))) t))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {A : Set.{u3} M} {α : Type.{u4}} {s : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α} {t : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α}, Iff (LE.le.{max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Preorder.toLE.{max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (PartialOrder.toPreorder.{max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (SetLike.instPartialOrder.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α)))) s t) (LE.le.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.instLESet.{max u4 u3} (α -> M)) (SetLike.coe.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α) s) (SetLike.coe.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α) t))
Case conversion may be inaccurate. Consider using '#align first_order.language.definable_set.le_iff FirstOrder.Language.DefinableSet.le_iffₓ'. -/
theorem le_iff : s ≤ t ↔ (s : Set (α → M)) ≤ (t : Set (α → M)) :=
  Iff.rfl
#align first_order.language.definable_set.le_iff FirstOrder.Language.DefinableSet.le_iff

#print FirstOrder.Language.DefinableSet.mem_top /-
@[simp]
theorem mem_top : x ∈ (⊤ : L.DefinableSet A α) :=
  mem_univ x
#align first_order.language.definable_set.mem_top FirstOrder.Language.DefinableSet.mem_top
-/

#print FirstOrder.Language.DefinableSet.not_mem_bot /-
@[simp]
theorem not_mem_bot {x : α → M} : ¬x ∈ (⊥ : L.DefinableSet A α) :=
  not_mem_empty x
#align first_order.language.definable_set.not_mem_bot FirstOrder.Language.DefinableSet.not_mem_bot
-/

#print FirstOrder.Language.DefinableSet.mem_sup /-
@[simp]
theorem mem_sup : x ∈ s ⊔ t ↔ x ∈ s ∨ x ∈ t :=
  Iff.rfl
#align first_order.language.definable_set.mem_sup FirstOrder.Language.DefinableSet.mem_sup
-/

#print FirstOrder.Language.DefinableSet.mem_inf /-
@[simp]
theorem mem_inf : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t :=
  Iff.rfl
#align first_order.language.definable_set.mem_inf FirstOrder.Language.DefinableSet.mem_inf
-/

#print FirstOrder.Language.DefinableSet.mem_compl /-
@[simp]
theorem mem_compl : x ∈ sᶜ ↔ ¬x ∈ s :=
  Iff.rfl
#align first_order.language.definable_set.mem_compl FirstOrder.Language.DefinableSet.mem_compl
-/

#print FirstOrder.Language.DefinableSet.mem_sdiff /-
@[simp]
theorem mem_sdiff : x ∈ s \ t ↔ x ∈ s ∧ ¬x ∈ t :=
  Iff.rfl
#align first_order.language.definable_set.mem_sdiff FirstOrder.Language.DefinableSet.mem_sdiff
-/

#print FirstOrder.Language.DefinableSet.coe_top /-
@[simp, norm_cast]
theorem coe_top : ((⊤ : L.DefinableSet A α) : Set (α → M)) = univ :=
  rfl
#align first_order.language.definable_set.coe_top FirstOrder.Language.DefinableSet.coe_top
-/

#print FirstOrder.Language.DefinableSet.coe_bot /-
@[simp, norm_cast]
theorem coe_bot : ((⊥ : L.DefinableSet A α) : Set (α → M)) = ∅ :=
  rfl
#align first_order.language.definable_set.coe_bot FirstOrder.Language.DefinableSet.coe_bot
-/

/- warning: first_order.language.definable_set.coe_sup -> FirstOrder.Language.DefinableSet.coe_sup is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {A : Set.{u3} M} {α : Type.{u4}} (s : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (t : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α), Eq.{succ (max u4 u3)} (Set.{max u4 u3} (α -> M)) ((fun (a : Type.{max u4 u3}) (b : Type.{max u4 u3}) [self : HasLiftT.{succ (max u4 u3), succ (max u4 u3)} a b] => self.0) (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (HasLiftT.mk.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (CoeTCₓ.coe.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (SetLike.Set.hasCoeT.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α)))) (Sup.sup.{max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (FirstOrder.Language.DefinableSet.instSup.{u1, u2, u3, u4} L M _inst_1 A α) s t)) (Union.union.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.hasUnion.{max u4 u3} (α -> M)) ((fun (a : Type.{max u4 u3}) (b : Type.{max u4 u3}) [self : HasLiftT.{succ (max u4 u3), succ (max u4 u3)} a b] => self.0) (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (HasLiftT.mk.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (CoeTCₓ.coe.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (SetLike.Set.hasCoeT.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α)))) s) ((fun (a : Type.{max u4 u3}) (b : Type.{max u4 u3}) [self : HasLiftT.{succ (max u4 u3), succ (max u4 u3)} a b] => self.0) (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (HasLiftT.mk.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (CoeTCₓ.coe.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (SetLike.Set.hasCoeT.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α)))) t))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {A : Set.{u3} M} {α : Type.{u4}} (s : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (t : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α), Eq.{max (succ u4) (succ u3)} (Set.{max u4 u3} (α -> M)) (SetLike.coe.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α) (Sup.sup.{max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (FirstOrder.Language.DefinableSet.instSup.{u1, u2, u3, u4} L M _inst_1 A α) s t)) (Union.union.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.instUnionSet.{max u4 u3} (α -> M)) (SetLike.coe.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α) s) (SetLike.coe.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α) t))
Case conversion may be inaccurate. Consider using '#align first_order.language.definable_set.coe_sup FirstOrder.Language.DefinableSet.coe_supₓ'. -/
@[simp, norm_cast]
theorem coe_sup (s t : L.DefinableSet A α) : (↑(s ⊔ t) : Set (α → M)) = s ∪ t :=
  rfl
#align first_order.language.definable_set.coe_sup FirstOrder.Language.DefinableSet.coe_sup

/- warning: first_order.language.definable_set.coe_inf -> FirstOrder.Language.DefinableSet.coe_inf is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {A : Set.{u3} M} {α : Type.{u4}} (s : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (t : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α), Eq.{succ (max u4 u3)} (Set.{max u4 u3} (α -> M)) ((fun (a : Type.{max u4 u3}) (b : Type.{max u4 u3}) [self : HasLiftT.{succ (max u4 u3), succ (max u4 u3)} a b] => self.0) (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (HasLiftT.mk.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (CoeTCₓ.coe.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (SetLike.Set.hasCoeT.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α)))) (Inf.inf.{max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (FirstOrder.Language.DefinableSet.instInf.{u1, u2, u3, u4} L M _inst_1 A α) s t)) (Inter.inter.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.hasInter.{max u4 u3} (α -> M)) ((fun (a : Type.{max u4 u3}) (b : Type.{max u4 u3}) [self : HasLiftT.{succ (max u4 u3), succ (max u4 u3)} a b] => self.0) (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (HasLiftT.mk.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (CoeTCₓ.coe.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (SetLike.Set.hasCoeT.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α)))) s) ((fun (a : Type.{max u4 u3}) (b : Type.{max u4 u3}) [self : HasLiftT.{succ (max u4 u3), succ (max u4 u3)} a b] => self.0) (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (HasLiftT.mk.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (CoeTCₓ.coe.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (SetLike.Set.hasCoeT.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α)))) t))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {A : Set.{u3} M} {α : Type.{u4}} (s : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (t : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α), Eq.{max (succ u4) (succ u3)} (Set.{max u4 u3} (α -> M)) (SetLike.coe.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α) (Inf.inf.{max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (FirstOrder.Language.DefinableSet.instInf.{u1, u2, u3, u4} L M _inst_1 A α) s t)) (Inter.inter.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.instInterSet.{max u4 u3} (α -> M)) (SetLike.coe.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α) s) (SetLike.coe.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α) t))
Case conversion may be inaccurate. Consider using '#align first_order.language.definable_set.coe_inf FirstOrder.Language.DefinableSet.coe_infₓ'. -/
@[simp, norm_cast]
theorem coe_inf (s t : L.DefinableSet A α) : (↑(s ⊓ t) : Set (α → M)) = s ∩ t :=
  rfl
#align first_order.language.definable_set.coe_inf FirstOrder.Language.DefinableSet.coe_inf

/- warning: first_order.language.definable_set.coe_compl -> FirstOrder.Language.DefinableSet.coe_compl is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {A : Set.{u3} M} {α : Type.{u4}} (s : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α), Eq.{succ (max u4 u3)} (Set.{max u4 u3} (α -> M)) ((fun (a : Type.{max u4 u3}) (b : Type.{max u4 u3}) [self : HasLiftT.{succ (max u4 u3), succ (max u4 u3)} a b] => self.0) (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (HasLiftT.mk.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (CoeTCₓ.coe.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (SetLike.Set.hasCoeT.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α)))) (HasCompl.compl.{max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (FirstOrder.Language.DefinableSet.instHasCompl.{u1, u2, u3, u4} L M _inst_1 A α) s)) (HasCompl.compl.{max u4 u3} (Set.{max u4 u3} (α -> M)) (BooleanAlgebra.toHasCompl.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.booleanAlgebra.{max u4 u3} (α -> M))) ((fun (a : Type.{max u4 u3}) (b : Type.{max u4 u3}) [self : HasLiftT.{succ (max u4 u3), succ (max u4 u3)} a b] => self.0) (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (HasLiftT.mk.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (CoeTCₓ.coe.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (SetLike.Set.hasCoeT.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α)))) s))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {A : Set.{u3} M} {α : Type.{u4}} (s : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α), Eq.{max (succ u4) (succ u3)} (Set.{max u4 u3} (α -> M)) (SetLike.coe.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α) (HasCompl.compl.{max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (FirstOrder.Language.DefinableSet.instHasCompl.{u1, u2, u3, u4} L M _inst_1 A α) s)) (HasCompl.compl.{max u4 u3} (Set.{max u4 u3} (α -> M)) (BooleanAlgebra.toHasCompl.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.instBooleanAlgebraSet.{max u4 u3} (α -> M))) (SetLike.coe.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α) s))
Case conversion may be inaccurate. Consider using '#align first_order.language.definable_set.coe_compl FirstOrder.Language.DefinableSet.coe_complₓ'. -/
@[simp, norm_cast]
theorem coe_compl (s : L.DefinableSet A α) : (↑(sᶜ) : Set (α → M)) = sᶜ :=
  rfl
#align first_order.language.definable_set.coe_compl FirstOrder.Language.DefinableSet.coe_compl

/- warning: first_order.language.definable_set.coe_sdiff -> FirstOrder.Language.DefinableSet.coe_sdiff is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {A : Set.{u3} M} {α : Type.{u4}} (s : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (t : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α), Eq.{succ (max u4 u3)} (Set.{max u4 u3} (α -> M)) ((fun (a : Type.{max u4 u3}) (b : Type.{max u4 u3}) [self : HasLiftT.{succ (max u4 u3), succ (max u4 u3)} a b] => self.0) (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (HasLiftT.mk.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (CoeTCₓ.coe.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (SetLike.Set.hasCoeT.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α)))) (SDiff.sdiff.{max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (FirstOrder.Language.DefinableSet.instSDiff.{u1, u2, u3, u4} L M _inst_1 A α) s t)) (SDiff.sdiff.{max u4 u3} (Set.{max u4 u3} (α -> M)) (BooleanAlgebra.toHasSdiff.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.booleanAlgebra.{max u4 u3} (α -> M))) ((fun (a : Type.{max u4 u3}) (b : Type.{max u4 u3}) [self : HasLiftT.{succ (max u4 u3), succ (max u4 u3)} a b] => self.0) (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (HasLiftT.mk.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (CoeTCₓ.coe.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (SetLike.Set.hasCoeT.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α)))) s) ((fun (a : Type.{max u4 u3}) (b : Type.{max u4 u3}) [self : HasLiftT.{succ (max u4 u3), succ (max u4 u3)} a b] => self.0) (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (HasLiftT.mk.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (CoeTCₓ.coe.{succ (max u4 u3), succ (max u4 u3)} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (Set.{max u4 u3} (α -> M)) (SetLike.Set.hasCoeT.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α)))) t))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {A : Set.{u3} M} {α : Type.{u4}} (s : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (t : FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α), Eq.{max (succ u4) (succ u3)} (Set.{max u4 u3} (α -> M)) (SetLike.coe.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α) (SDiff.sdiff.{max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (FirstOrder.Language.DefinableSet.instSDiff.{u1, u2, u3, u4} L M _inst_1 A α) s t)) (SDiff.sdiff.{max u4 u3} (Set.{max u4 u3} (α -> M)) (Set.instSDiffSet.{max u4 u3} (α -> M)) (SetLike.coe.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α) s) (SetLike.coe.{max u4 u3, max u4 u3} (FirstOrder.Language.DefinableSet.{u1, u2, u3, u4} L M _inst_1 A α) (α -> M) (FirstOrder.Language.DefinableSet.instSetLike.{u1, u2, u3, u4} L M _inst_1 A α) t))
Case conversion may be inaccurate. Consider using '#align first_order.language.definable_set.coe_sdiff FirstOrder.Language.DefinableSet.coe_sdiffₓ'. -/
@[simp, norm_cast]
theorem coe_sdiff (s t : L.DefinableSet A α) : (↑(s \ t) : Set (α → M)) = s \ t :=
  rfl
#align first_order.language.definable_set.coe_sdiff FirstOrder.Language.DefinableSet.coe_sdiff

instance : BooleanAlgebra (L.DefinableSet A α) :=
  Subtype.coe_injective.BooleanAlgebra _ coe_sup coe_inf coe_top coe_bot coe_compl coe_sdiff

end DefinableSet

end Language

end FirstOrder

