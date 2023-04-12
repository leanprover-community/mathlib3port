/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard

! This file was ported from Lean 3 source module ring_theory.noetherian
! leanprover-community/mathlib commit 210657c4ea4a4a7b234392f70a3a2a83346dfa90
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.Algebra.Algebra.Tower
import Mathbin.Algebra.Ring.Idempotents
import Mathbin.GroupTheory.Finiteness
import Mathbin.LinearAlgebra.LinearIndependent
import Mathbin.Order.CompactlyGenerated
import Mathbin.Order.OrderIsoNat
import Mathbin.RingTheory.Finiteness
import Mathbin.RingTheory.Nilpotent

/-!
# Noetherian rings and modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The following are equivalent for a module M over a ring R:
1. Every increasing chain of submodules M₁ ⊆ M₂ ⊆ M₃ ⊆ ⋯ eventually stabilises.
2. Every submodule is finitely generated.

A module satisfying these equivalent conditions is said to be a *Noetherian* R-module.
A ring is a *Noetherian ring* if it is Noetherian as a module over itself.

(Note that we do not assume yet that our rings are commutative,
so perhaps this should be called "left Noetherian".
To avoid cumbersome names once we specialize to the commutative case,
we don't make this explicit in the declaration names.)

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `is_noetherian R M` is the proposition that `M` is a Noetherian `R`-module. It is a class,
  implemented as the predicate that all `R`-submodules of `M` are finitely generated.

## Main statements

* `is_noetherian_iff_well_founded` is the theorem that an R-module M is Noetherian iff
  `>` is well-founded on `submodule R M`.

Note that the Hilbert basis theorem, that if a commutative ring R is Noetherian then so is R[X],
is proved in `ring_theory.polynomial`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel1967]

## Tags

Noetherian, noetherian, Noetherian ring, Noetherian module, noetherian ring, noetherian module

-/


open Set

open BigOperators Pointwise

#print IsNoetherian /-
/-- `is_noetherian R M` is the proposition that `M` is a Noetherian `R`-module,
implemented as the predicate that all `R`-submodules of `M` are finitely generated.
-/
class IsNoetherian (R M) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  noetherian : ∀ s : Submodule R M, s.Fg
#align is_noetherian IsNoetherian
-/

section

variable {R : Type _} {M : Type _} {P : Type _}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid P]

variable [Module R M] [Module R P]

open IsNoetherian

include R

/- warning: is_noetherian_def -> isNoetherian_def is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_4 : Module.{u1, u2} R M _inst_1 _inst_2], Iff (IsNoetherian.{u1, u2} R M _inst_1 _inst_2 _inst_4) (forall (s : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4), Submodule.Fg.{u1, u2} R M _inst_1 _inst_2 _inst_4 s)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_4 : Module.{u2, u1} R M _inst_1 _inst_2], Iff (IsNoetherian.{u2, u1} R M _inst_1 _inst_2 _inst_4) (forall (s : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4), Submodule.Fg.{u2, u1} R M _inst_1 _inst_2 _inst_4 s)
Case conversion may be inaccurate. Consider using '#align is_noetherian_def isNoetherian_defₓ'. -/
/-- An R-module is Noetherian iff all its submodules are finitely-generated. -/
theorem isNoetherian_def : IsNoetherian R M ↔ ∀ s : Submodule R M, s.Fg :=
  ⟨fun h => h.noetherian, IsNoetherian.mk⟩
#align is_noetherian_def isNoetherian_def

/- warning: is_noetherian_submodule -> isNoetherian_submodule is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_4 : Module.{u1, u2} R M _inst_1 _inst_2] {N : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4}, Iff (IsNoetherian.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) M (Submodule.setLike.{u1, u2} R M _inst_1 _inst_2 _inst_4)) N) _inst_1 (Submodule.addCommMonoid.{u1, u2} R M _inst_1 _inst_2 _inst_4 N) (Submodule.module.{u1, u2} R M _inst_1 _inst_2 _inst_4 N)) (forall (s : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4), (LE.le.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) (Preorder.toLE.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) (Submodule.completeLattice.{u1, u2} R M _inst_1 _inst_2 _inst_4))))) s N) -> (Submodule.Fg.{u1, u2} R M _inst_1 _inst_2 _inst_4 s))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_4 : Module.{u2, u1} R M _inst_1 _inst_2] {N : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4}, Iff (IsNoetherian.{u2, u1} R (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) M (Submodule.setLike.{u2, u1} R M _inst_1 _inst_2 _inst_4)) x N)) _inst_1 (Submodule.addCommMonoid.{u2, u1} R M _inst_1 _inst_2 _inst_4 N) (Submodule.module.{u2, u1} R M _inst_1 _inst_2 _inst_4 N)) (forall (s : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4), (LE.le.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (Preorder.toLE.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (PartialOrder.toPreorder.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (Submodule.completeLattice.{u2, u1} R M _inst_1 _inst_2 _inst_4))))) s N) -> (Submodule.Fg.{u2, u1} R M _inst_1 _inst_2 _inst_4 s))
Case conversion may be inaccurate. Consider using '#align is_noetherian_submodule isNoetherian_submoduleₓ'. -/
theorem isNoetherian_submodule {N : Submodule R M} :
    IsNoetherian R N ↔ ∀ s : Submodule R M, s ≤ N → s.Fg :=
  by
  refine'
    ⟨fun ⟨hn⟩ => fun s hs =>
      have : s ≤ N.subtype.range := N.range_subtype.symm ▸ hs
      Submodule.map_comap_eq_self this ▸ (hn _).map _,
      fun h => ⟨fun s => _⟩⟩
  have f := (Submodule.equivMapOfInjective N.subtype Subtype.val_injective s).symm
  have h₁ := h (s.map N.subtype) (Submodule.map_subtype_le N s)
  have h₂ : (⊤ : Submodule R (s.map N.subtype)).map f = ⊤ := by simp
  have h₃ := ((Submodule.fg_top _).2 h₁).map (↑f : _ →ₗ[R] s)
  exact (Submodule.fg_top _).1 (h₂ ▸ h₃)
#align is_noetherian_submodule isNoetherian_submodule

/- warning: is_noetherian_submodule_left -> isNoetherian_submodule_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_4 : Module.{u1, u2} R M _inst_1 _inst_2] {N : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4}, Iff (IsNoetherian.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) M (Submodule.setLike.{u1, u2} R M _inst_1 _inst_2 _inst_4)) N) _inst_1 (Submodule.addCommMonoid.{u1, u2} R M _inst_1 _inst_2 _inst_4 N) (Submodule.module.{u1, u2} R M _inst_1 _inst_2 _inst_4 N)) (forall (s : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4), Submodule.Fg.{u1, u2} R M _inst_1 _inst_2 _inst_4 (Inf.inf.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) (Submodule.hasInf.{u1, u2} R M _inst_1 _inst_2 _inst_4) N s))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_4 : Module.{u2, u1} R M _inst_1 _inst_2] {N : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4}, Iff (IsNoetherian.{u2, u1} R (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) M (Submodule.setLike.{u2, u1} R M _inst_1 _inst_2 _inst_4)) x N)) _inst_1 (Submodule.addCommMonoid.{u2, u1} R M _inst_1 _inst_2 _inst_4 N) (Submodule.module.{u2, u1} R M _inst_1 _inst_2 _inst_4 N)) (forall (s : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4), Submodule.Fg.{u2, u1} R M _inst_1 _inst_2 _inst_4 (Inf.inf.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (Submodule.instInfSubmodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) N s))
Case conversion may be inaccurate. Consider using '#align is_noetherian_submodule_left isNoetherian_submodule_leftₓ'. -/
theorem isNoetherian_submodule_left {N : Submodule R M} :
    IsNoetherian R N ↔ ∀ s : Submodule R M, (N ⊓ s).Fg :=
  isNoetherian_submodule.trans ⟨fun H s => H _ inf_le_left, fun H s hs => inf_of_le_right hs ▸ H _⟩
#align is_noetherian_submodule_left isNoetherian_submodule_left

/- warning: is_noetherian_submodule_right -> isNoetherian_submodule_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_4 : Module.{u1, u2} R M _inst_1 _inst_2] {N : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4}, Iff (IsNoetherian.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) M (Submodule.setLike.{u1, u2} R M _inst_1 _inst_2 _inst_4)) N) _inst_1 (Submodule.addCommMonoid.{u1, u2} R M _inst_1 _inst_2 _inst_4 N) (Submodule.module.{u1, u2} R M _inst_1 _inst_2 _inst_4 N)) (forall (s : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4), Submodule.Fg.{u1, u2} R M _inst_1 _inst_2 _inst_4 (Inf.inf.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) (Submodule.hasInf.{u1, u2} R M _inst_1 _inst_2 _inst_4) s N))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_4 : Module.{u2, u1} R M _inst_1 _inst_2] {N : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4}, Iff (IsNoetherian.{u2, u1} R (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) M (Submodule.setLike.{u2, u1} R M _inst_1 _inst_2 _inst_4)) x N)) _inst_1 (Submodule.addCommMonoid.{u2, u1} R M _inst_1 _inst_2 _inst_4 N) (Submodule.module.{u2, u1} R M _inst_1 _inst_2 _inst_4 N)) (forall (s : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4), Submodule.Fg.{u2, u1} R M _inst_1 _inst_2 _inst_4 (Inf.inf.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (Submodule.instInfSubmodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) s N))
Case conversion may be inaccurate. Consider using '#align is_noetherian_submodule_right isNoetherian_submodule_rightₓ'. -/
theorem isNoetherian_submodule_right {N : Submodule R M} :
    IsNoetherian R N ↔ ∀ s : Submodule R M, (s ⊓ N).Fg :=
  isNoetherian_submodule.trans ⟨fun H s => H _ inf_le_right, fun H s hs => inf_of_le_left hs ▸ H _⟩
#align is_noetherian_submodule_right isNoetherian_submodule_right

#print isNoetherian_submodule' /-
instance isNoetherian_submodule' [IsNoetherian R M] (N : Submodule R M) : IsNoetherian R N :=
  isNoetherian_submodule.2 fun _ _ => IsNoetherian.noetherian _
#align is_noetherian_submodule' isNoetherian_submodule'
-/

/- warning: is_noetherian_of_le -> isNoetherian_of_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_4 : Module.{u1, u2} R M _inst_1 _inst_2] {s : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4} {t : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4} [ht : IsNoetherian.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) M (Submodule.setLike.{u1, u2} R M _inst_1 _inst_2 _inst_4)) t) _inst_1 (Submodule.addCommMonoid.{u1, u2} R M _inst_1 _inst_2 _inst_4 t) (Submodule.module.{u1, u2} R M _inst_1 _inst_2 _inst_4 t)], (LE.le.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) (Preorder.toLE.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) (Submodule.completeLattice.{u1, u2} R M _inst_1 _inst_2 _inst_4))))) s t) -> (IsNoetherian.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) M (Submodule.setLike.{u1, u2} R M _inst_1 _inst_2 _inst_4)) s) _inst_1 (Submodule.addCommMonoid.{u1, u2} R M _inst_1 _inst_2 _inst_4 s) (Submodule.module.{u1, u2} R M _inst_1 _inst_2 _inst_4 s))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_4 : Module.{u2, u1} R M _inst_1 _inst_2] {s : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4} {t : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4} [ht : IsNoetherian.{u2, u1} R (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) M (Submodule.setLike.{u2, u1} R M _inst_1 _inst_2 _inst_4)) x t)) _inst_1 (Submodule.addCommMonoid.{u2, u1} R M _inst_1 _inst_2 _inst_4 t) (Submodule.module.{u2, u1} R M _inst_1 _inst_2 _inst_4 t)], (LE.le.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (Preorder.toLE.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (PartialOrder.toPreorder.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (Submodule.completeLattice.{u2, u1} R M _inst_1 _inst_2 _inst_4))))) s t) -> (IsNoetherian.{u2, u1} R (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) M (Submodule.setLike.{u2, u1} R M _inst_1 _inst_2 _inst_4)) x s)) _inst_1 (Submodule.addCommMonoid.{u2, u1} R M _inst_1 _inst_2 _inst_4 s) (Submodule.module.{u2, u1} R M _inst_1 _inst_2 _inst_4 s))
Case conversion may be inaccurate. Consider using '#align is_noetherian_of_le isNoetherian_of_leₓ'. -/
theorem isNoetherian_of_le {s t : Submodule R M} [ht : IsNoetherian R t] (h : s ≤ t) :
    IsNoetherian R s :=
  isNoetherian_submodule.mpr fun s' hs' => isNoetherian_submodule.mp ht _ (le_trans hs' h)
#align is_noetherian_of_le isNoetherian_of_le

variable (M)

/- warning: is_noetherian_of_surjective -> isNoetherian_of_surjective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} (M : Type.{u2}) {P : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : AddCommMonoid.{u3} P] [_inst_4 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_5 : Module.{u1, u3} R P _inst_1 _inst_3] (f : LinearMap.{u1, u1, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M P _inst_2 _inst_3 _inst_4 _inst_5), (Eq.{succ u3} (Submodule.{u1, u3} R P _inst_1 _inst_3 _inst_5) (LinearMap.range.{u1, u1, u2, u3, max u2 u3} R R M P _inst_1 _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (LinearMap.{u1, u1, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M P _inst_2 _inst_3 _inst_4 _inst_5) (LinearMap.semilinearMapClass.{u1, u1, u2, u3} R R M P _inst_1 _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (RingHomSurjective.ids.{u1} R _inst_1) f) (Top.top.{u3} (Submodule.{u1, u3} R P _inst_1 _inst_3 _inst_5) (Submodule.hasTop.{u1, u3} R P _inst_1 _inst_3 _inst_5))) -> (forall [_inst_6 : IsNoetherian.{u1, u2} R M _inst_1 _inst_2 _inst_4], IsNoetherian.{u1, u3} R P _inst_1 _inst_3 _inst_5)
but is expected to have type
  forall {R : Type.{u3}} (M : Type.{u2}) {P : Type.{u1}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : AddCommMonoid.{u1} P] [_inst_4 : Module.{u3, u2} R M _inst_1 _inst_2] [_inst_5 : Module.{u3, u1} R P _inst_1 _inst_3] (f : LinearMap.{u3, u3, u2, u1} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) M P _inst_2 _inst_3 _inst_4 _inst_5), (Eq.{succ u1} (Submodule.{u3, u1} R P _inst_1 _inst_3 _inst_5) (LinearMap.range.{u3, u3, u2, u1, max u2 u1} R R M P _inst_1 _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (LinearMap.{u3, u3, u2, u1} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) M P _inst_2 _inst_3 _inst_4 _inst_5) (LinearMap.instSemilinearMapClassLinearMap.{u3, u3, u2, u1} R R M P _inst_1 _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (RingHomSurjective.ids.{u3} R _inst_1) f) (Top.top.{u1} (Submodule.{u3, u1} R P _inst_1 _inst_3 _inst_5) (Submodule.instTopSubmodule.{u3, u1} R P _inst_1 _inst_3 _inst_5))) -> (forall [_inst_6 : IsNoetherian.{u3, u2} R M _inst_1 _inst_2 _inst_4], IsNoetherian.{u3, u1} R P _inst_1 _inst_3 _inst_5)
Case conversion may be inaccurate. Consider using '#align is_noetherian_of_surjective isNoetherian_of_surjectiveₓ'. -/
theorem isNoetherian_of_surjective (f : M →ₗ[R] P) (hf : f.range = ⊤) [IsNoetherian R M] :
    IsNoetherian R P :=
  ⟨fun s =>
    have : (s.comap f).map f = s := Submodule.map_comap_eq_self <| hf.symm ▸ le_top
    this ▸ (noetherian _).map _⟩
#align is_noetherian_of_surjective isNoetherian_of_surjective

variable {M}

/- warning: is_noetherian_of_linear_equiv -> isNoetherian_of_linearEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {P : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : AddCommMonoid.{u3} P] [_inst_4 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_5 : Module.{u1, u3} R P _inst_1 _inst_3], (LinearEquiv.{u1, u1, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M P _inst_2 _inst_3 _inst_4 _inst_5) -> (forall [_inst_6 : IsNoetherian.{u1, u2} R M _inst_1 _inst_2 _inst_4], IsNoetherian.{u1, u3} R P _inst_1 _inst_3 _inst_5)
but is expected to have type
  forall {R : Type.{u3}} {M : Type.{u2}} {P : Type.{u1}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : AddCommMonoid.{u1} P] [_inst_4 : Module.{u3, u2} R M _inst_1 _inst_2] [_inst_5 : Module.{u3, u1} R P _inst_1 _inst_3], (LinearEquiv.{u3, u3, u2, u1} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) M P _inst_2 _inst_3 _inst_4 _inst_5) -> (forall [_inst_6 : IsNoetherian.{u3, u2} R M _inst_1 _inst_2 _inst_4], IsNoetherian.{u3, u1} R P _inst_1 _inst_3 _inst_5)
Case conversion may be inaccurate. Consider using '#align is_noetherian_of_linear_equiv isNoetherian_of_linearEquivₓ'. -/
theorem isNoetherian_of_linearEquiv (f : M ≃ₗ[R] P) [IsNoetherian R M] : IsNoetherian R P :=
  isNoetherian_of_surjective _ f.toLinearMap f.range
#align is_noetherian_of_linear_equiv isNoetherian_of_linearEquiv

/- warning: is_noetherian_top_iff -> isNoetherian_top_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_4 : Module.{u1, u2} R M _inst_1 _inst_2], Iff (IsNoetherian.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) M (Submodule.setLike.{u1, u2} R M _inst_1 _inst_2 _inst_4)) (Top.top.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) (Submodule.hasTop.{u1, u2} R M _inst_1 _inst_2 _inst_4))) _inst_1 (Submodule.addCommMonoid.{u1, u2} R M _inst_1 _inst_2 _inst_4 (Top.top.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) (Submodule.hasTop.{u1, u2} R M _inst_1 _inst_2 _inst_4))) (Submodule.module.{u1, u2} R M _inst_1 _inst_2 _inst_4 (Top.top.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4) (Submodule.hasTop.{u1, u2} R M _inst_1 _inst_2 _inst_4)))) (IsNoetherian.{u1, u2} R M _inst_1 _inst_2 _inst_4)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_4 : Module.{u2, u1} R M _inst_1 _inst_2], Iff (IsNoetherian.{u2, u1} R (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) M (Submodule.setLike.{u2, u1} R M _inst_1 _inst_2 _inst_4)) x (Top.top.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (Submodule.instTopSubmodule.{u2, u1} R M _inst_1 _inst_2 _inst_4)))) _inst_1 (Submodule.addCommMonoid.{u2, u1} R M _inst_1 _inst_2 _inst_4 (Top.top.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (Submodule.instTopSubmodule.{u2, u1} R M _inst_1 _inst_2 _inst_4))) (Submodule.module.{u2, u1} R M _inst_1 _inst_2 _inst_4 (Top.top.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_4) (Submodule.instTopSubmodule.{u2, u1} R M _inst_1 _inst_2 _inst_4)))) (IsNoetherian.{u2, u1} R M _inst_1 _inst_2 _inst_4)
Case conversion may be inaccurate. Consider using '#align is_noetherian_top_iff isNoetherian_top_iffₓ'. -/
theorem isNoetherian_top_iff : IsNoetherian R (⊤ : Submodule R M) ↔ IsNoetherian R M :=
  by
  constructor <;> intro h
  · exact isNoetherian_of_linearEquiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl)
  · exact isNoetherian_of_linearEquiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl).symm
#align is_noetherian_top_iff isNoetherian_top_iff

/- warning: is_noetherian_of_injective -> isNoetherian_of_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {P : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : AddCommMonoid.{u3} P] [_inst_4 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_5 : Module.{u1, u3} R P _inst_1 _inst_3] [_inst_6 : IsNoetherian.{u1, u3} R P _inst_1 _inst_3 _inst_5] (f : LinearMap.{u1, u1, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M P _inst_2 _inst_3 _inst_4 _inst_5), (Function.Injective.{succ u2, succ u3} M P (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LinearMap.{u1, u1, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M P _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LinearMap.{u1, u1, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M P _inst_2 _inst_3 _inst_4 _inst_5) => M -> P) (LinearMap.hasCoeToFun.{u1, u1, u2, u3} R R M P _inst_1 _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) f)) -> (IsNoetherian.{u1, u2} R M _inst_1 _inst_2 _inst_4)
but is expected to have type
  forall {R : Type.{u3}} {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : AddCommMonoid.{u2} P] [_inst_4 : Module.{u3, u1} R M _inst_1 _inst_2] [_inst_5 : Module.{u3, u2} R P _inst_1 _inst_3] [_inst_6 : IsNoetherian.{u3, u2} R P _inst_1 _inst_3 _inst_5] (f : LinearMap.{u3, u3, u1, u2} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) M P _inst_2 _inst_3 _inst_4 _inst_5), (Function.Injective.{succ u1, succ u2} M P (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (LinearMap.{u3, u3, u1, u2} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) M P _inst_2 _inst_3 _inst_4 _inst_5) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : M) => P) _x) (LinearMap.instFunLikeLinearMap.{u3, u3, u1, u2} R R M P _inst_1 _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) f)) -> (IsNoetherian.{u3, u1} R M _inst_1 _inst_2 _inst_4)
Case conversion may be inaccurate. Consider using '#align is_noetherian_of_injective isNoetherian_of_injectiveₓ'. -/
theorem isNoetherian_of_injective [IsNoetherian R P] (f : M →ₗ[R] P) (hf : Function.Injective f) :
    IsNoetherian R M :=
  isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f hf).symm
#align is_noetherian_of_injective isNoetherian_of_injective

/- warning: fg_of_injective -> fg_of_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {P : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : AddCommMonoid.{u3} P] [_inst_4 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_5 : Module.{u1, u3} R P _inst_1 _inst_3] [_inst_6 : IsNoetherian.{u1, u3} R P _inst_1 _inst_3 _inst_5] {N : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_4} (f : LinearMap.{u1, u1, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M P _inst_2 _inst_3 _inst_4 _inst_5), (Function.Injective.{succ u2, succ u3} M P (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LinearMap.{u1, u1, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M P _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LinearMap.{u1, u1, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M P _inst_2 _inst_3 _inst_4 _inst_5) => M -> P) (LinearMap.hasCoeToFun.{u1, u1, u2, u3} R R M P _inst_1 _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) f)) -> (Submodule.Fg.{u1, u2} R M _inst_1 _inst_2 _inst_4 N)
but is expected to have type
  forall {R : Type.{u3}} {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : AddCommMonoid.{u2} P] [_inst_4 : Module.{u3, u1} R M _inst_1 _inst_2] [_inst_5 : Module.{u3, u2} R P _inst_1 _inst_3] [_inst_6 : IsNoetherian.{u3, u2} R P _inst_1 _inst_3 _inst_5] {N : Submodule.{u3, u1} R M _inst_1 _inst_2 _inst_4} (f : LinearMap.{u3, u3, u1, u2} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) M P _inst_2 _inst_3 _inst_4 _inst_5), (Function.Injective.{succ u1, succ u2} M P (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (LinearMap.{u3, u3, u1, u2} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) M P _inst_2 _inst_3 _inst_4 _inst_5) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : M) => P) _x) (LinearMap.instFunLikeLinearMap.{u3, u3, u1, u2} R R M P _inst_1 _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) f)) -> (Submodule.Fg.{u3, u1} R M _inst_1 _inst_2 _inst_4 N)
Case conversion may be inaccurate. Consider using '#align fg_of_injective fg_of_injectiveₓ'. -/
theorem fg_of_injective [IsNoetherian R P] {N : Submodule R M} (f : M →ₗ[R] P)
    (hf : Function.Injective f) : N.Fg :=
  @IsNoetherian.noetherian _ _ _ (isNoetherian_of_injective f hf) N
#align fg_of_injective fg_of_injective

end

namespace Module

variable {R M N : Type _}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

variable (R M)

#print Module.IsNoetherian.finite /-
-- see Note [lower instance priority]
instance (priority := 100) IsNoetherian.finite [IsNoetherian R M] : Finite R M :=
  ⟨IsNoetherian.noetherian ⊤⟩
#align module.is_noetherian.finite Module.IsNoetherian.finite
-/

variable {R M}

/- warning: module.finite.of_injective -> Module.Finite.of_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : AddCommMonoid.{u3} N] [_inst_4 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_5 : Module.{u1, u3} R N _inst_1 _inst_3] [_inst_6 : IsNoetherian.{u1, u3} R N _inst_1 _inst_3 _inst_5] (f : LinearMap.{u1, u1, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M N _inst_2 _inst_3 _inst_4 _inst_5), (Function.Injective.{succ u2, succ u3} M N (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LinearMap.{u1, u1, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M N _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LinearMap.{u1, u1, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) M N _inst_2 _inst_3 _inst_4 _inst_5) => M -> N) (LinearMap.hasCoeToFun.{u1, u1, u2, u3} R R M N _inst_1 _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) f)) -> (Module.Finite.{u1, u2} R M _inst_1 _inst_2 _inst_4)
but is expected to have type
  forall {R : Type.{u3}} {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : AddCommMonoid.{u2} N] [_inst_4 : Module.{u3, u1} R M _inst_1 _inst_2] [_inst_5 : Module.{u3, u2} R N _inst_1 _inst_3] [_inst_6 : IsNoetherian.{u3, u2} R N _inst_1 _inst_3 _inst_5] (f : LinearMap.{u3, u3, u1, u2} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) M N _inst_2 _inst_3 _inst_4 _inst_5), (Function.Injective.{succ u1, succ u2} M N (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (LinearMap.{u3, u3, u1, u2} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) M N _inst_2 _inst_3 _inst_4 _inst_5) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : M) => N) _x) (LinearMap.instFunLikeLinearMap.{u3, u3, u1, u2} R R M N _inst_1 _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) f)) -> (Module.Finite.{u3, u1} R M _inst_1 _inst_2 _inst_4)
Case conversion may be inaccurate. Consider using '#align module.finite.of_injective Module.Finite.of_injectiveₓ'. -/
theorem Finite.of_injective [IsNoetherian R N] (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Finite R M :=
  ⟨fg_of_injective f hf⟩
#align module.finite.of_injective Module.Finite.of_injective

end Module

section

variable {R : Type _} {M : Type _} {P : Type _}

variable [Ring R] [AddCommGroup M] [AddCommGroup P]

variable [Module R M] [Module R P]

open IsNoetherian

include R

/- warning: is_noetherian_of_ker_bot -> isNoetherian_of_ker_bot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {P : Type.{u3}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : AddCommGroup.{u3} P] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_5 : Module.{u1, u3} R P (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3)] [_inst_6 : IsNoetherian.{u1, u3} R P (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3) _inst_5] (f : LinearMap.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M P (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3) _inst_4 _inst_5), (Eq.{succ u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4) (LinearMap.ker.{u1, u1, u2, u3, max u2 u3} R R M P (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3) _inst_4 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (LinearMap.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M P (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3) _inst_4 _inst_5) (LinearMap.semilinearMapClass.{u1, u1, u2, u3} R R M P (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3) _inst_4 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) f) (Bot.bot.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4) (Submodule.hasBot.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4))) -> (IsNoetherian.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4)
but is expected to have type
  forall {R : Type.{u3}} {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : Ring.{u3} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : AddCommGroup.{u2} P] [_inst_4 : Module.{u3, u1} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] [_inst_5 : Module.{u3, u2} R P (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} P _inst_3)] [_inst_6 : IsNoetherian.{u3, u2} R P (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} P _inst_3) _inst_5] (f : LinearMap.{u3, u3, u1, u2} R R (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1))) M P (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} P _inst_3) _inst_4 _inst_5), (Eq.{succ u1} (Submodule.{u3, u1} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_4) (LinearMap.ker.{u3, u3, u1, u2, max u1 u2} R R M P (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} P _inst_3) _inst_4 _inst_5 (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1))) (LinearMap.{u3, u3, u1, u2} R R (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1))) M P (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} P _inst_3) _inst_4 _inst_5) (LinearMap.instSemilinearMapClassLinearMap.{u3, u3, u1, u2} R R M P (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} P _inst_3) _inst_4 _inst_5 (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1)))) f) (Bot.bot.{u1} (Submodule.{u3, u1} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_4) (Submodule.instBotSubmodule.{u3, u1} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_4))) -> (IsNoetherian.{u3, u1} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_4)
Case conversion may be inaccurate. Consider using '#align is_noetherian_of_ker_bot isNoetherian_of_ker_botₓ'. -/
theorem isNoetherian_of_ker_bot [IsNoetherian R P] (f : M →ₗ[R] P) (hf : f.ker = ⊥) :
    IsNoetherian R M :=
  isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f <| LinearMap.ker_eq_bot.mp hf).symm
#align is_noetherian_of_ker_bot isNoetherian_of_ker_bot

/- warning: fg_of_ker_bot -> fg_of_ker_bot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {P : Type.{u3}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : AddCommGroup.{u3} P] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_5 : Module.{u1, u3} R P (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3)] [_inst_6 : IsNoetherian.{u1, u3} R P (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3) _inst_5] {N : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4} (f : LinearMap.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M P (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3) _inst_4 _inst_5), (Eq.{succ u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4) (LinearMap.ker.{u1, u1, u2, u3, max u2 u3} R R M P (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3) _inst_4 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (LinearMap.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M P (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3) _inst_4 _inst_5) (LinearMap.semilinearMapClass.{u1, u1, u2, u3} R R M P (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3) _inst_4 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) f) (Bot.bot.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4) (Submodule.hasBot.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4))) -> (Submodule.Fg.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 N)
but is expected to have type
  forall {R : Type.{u3}} {M : Type.{u1}} {P : Type.{u2}} [_inst_1 : Ring.{u3} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : AddCommGroup.{u2} P] [_inst_4 : Module.{u3, u1} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] [_inst_5 : Module.{u3, u2} R P (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} P _inst_3)] [_inst_6 : IsNoetherian.{u3, u2} R P (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} P _inst_3) _inst_5] {N : Submodule.{u3, u1} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_4} (f : LinearMap.{u3, u3, u1, u2} R R (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1))) M P (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} P _inst_3) _inst_4 _inst_5), (Eq.{succ u1} (Submodule.{u3, u1} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_4) (LinearMap.ker.{u3, u3, u1, u2, max u1 u2} R R M P (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} P _inst_3) _inst_4 _inst_5 (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1))) (LinearMap.{u3, u3, u1, u2} R R (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1))) M P (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} P _inst_3) _inst_4 _inst_5) (LinearMap.instSemilinearMapClassLinearMap.{u3, u3, u1, u2} R R M P (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} P _inst_3) _inst_4 _inst_5 (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1)))) f) (Bot.bot.{u1} (Submodule.{u3, u1} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_4) (Submodule.instBotSubmodule.{u3, u1} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_4))) -> (Submodule.Fg.{u3, u1} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_4 N)
Case conversion may be inaccurate. Consider using '#align fg_of_ker_bot fg_of_ker_botₓ'. -/
theorem fg_of_ker_bot [IsNoetherian R P] {N : Submodule R M} (f : M →ₗ[R] P) (hf : f.ker = ⊥) :
    N.Fg :=
  @IsNoetherian.noetherian _ _ _ (isNoetherian_of_ker_bot f hf) N
#align fg_of_ker_bot fg_of_ker_bot

/- warning: is_noetherian_prod -> isNoetherian_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {P : Type.{u3}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : AddCommGroup.{u3} P] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_5 : Module.{u1, u3} R P (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3)] [_inst_6 : IsNoetherian.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4] [_inst_7 : IsNoetherian.{u1, u3} R P (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3) _inst_5], IsNoetherian.{u1, max u2 u3} R (Prod.{u2, u3} M P) (Ring.toSemiring.{u1} R _inst_1) (Prod.addCommMonoid.{u2, u3} M P (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3)) (Prod.module.{u1, u2, u3} R M P (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3) _inst_4 _inst_5)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} {P : Type.{u3}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : AddCommGroup.{u3} P] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_5 : Module.{u1, u3} R P (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3)] [_inst_6 : IsNoetherian.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4] [_inst_7 : IsNoetherian.{u1, u3} R P (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3) _inst_5], IsNoetherian.{u1, max u3 u2} R (Prod.{u2, u3} M P) (Ring.toSemiring.{u1} R _inst_1) (Prod.instAddCommMonoidSum.{u2, u3} M P (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3)) (Prod.module.{u1, u2, u3} R M P (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} P _inst_3) _inst_4 _inst_5)
Case conversion may be inaccurate. Consider using '#align is_noetherian_prod isNoetherian_prodₓ'. -/
instance isNoetherian_prod [IsNoetherian R M] [IsNoetherian R P] : IsNoetherian R (M × P) :=
  ⟨fun s =>
    Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd R M P) (noetherian _) <|
      have : s ⊓ LinearMap.ker (LinearMap.snd R M P) ≤ LinearMap.range (LinearMap.inl R M P) :=
        fun x ⟨hx1, hx2⟩ => ⟨x.1, Prod.ext rfl <| Eq.symm <| LinearMap.mem_ker.1 hx2⟩
      Submodule.map_comap_eq_self this ▸ (noetherian _).map _⟩
#align is_noetherian_prod isNoetherian_prod

#print isNoetherian_pi /-
instance isNoetherian_pi {R ι : Type _} {M : ι → Type _} [Ring R] [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] [Finite ι] [∀ i, IsNoetherian R (M i)] : IsNoetherian R (∀ i, M i) :=
  by
  cases nonempty_fintype ι
  haveI := Classical.decEq ι
  suffices on_finset : ∀ s : Finset ι, IsNoetherian R (∀ i : s, M i)
  · let coe_e := Equiv.subtypeUnivEquiv Finset.mem_univ
    letI : IsNoetherian R (∀ i : Finset.univ, M (coe_e i)) := on_finset Finset.univ
    exact isNoetherian_of_linearEquiv (LinearEquiv.piCongrLeft R M coe_e)
  intro s
  induction' s using Finset.induction with a s has ih
  · exact ⟨fun s => by convert Submodule.fg_bot⟩
  refine'
    @isNoetherian_of_linearEquiv _ _ _ _ _ _ _ _ _ (@isNoetherian_prod _ (M a) _ _ _ _ _ _ _ ih)
  fconstructor
  ·
    exact fun f i =>
      Or.by_cases (Finset.mem_insert.1 i.2) (fun h : i.1 = a => show M i.1 from Eq.recOn h.symm f.1)
        fun h : i.1 ∈ s => show M i.1 from f.2 ⟨i.1, h⟩
  · intro f g
    ext i
    unfold Or.by_cases
    cases' i with i hi
    rcases Finset.mem_insert.1 hi with (rfl | h)
    · change _ = _ + _
      simp only [dif_pos]
      rfl
    · change _ = _ + _
      have : ¬i = a := by
        rintro rfl
        exact has h
      simp only [dif_neg this, dif_pos h]
      rfl
  · intro c f
    ext i
    unfold Or.by_cases
    cases' i with i hi
    rcases Finset.mem_insert.1 hi with (rfl | h)
    · change _ = c • _
      simp only [dif_pos]
      rfl
    · change _ = c • _
      have : ¬i = a := by
        rintro rfl
        exact has h
      simp only [dif_neg this, dif_pos h]
      rfl
  ·
    exact fun f =>
      (f ⟨a, Finset.mem_insert_self _ _⟩, fun i => f ⟨i.1, Finset.mem_insert_of_mem i.2⟩)
  · intro f
    apply Prod.ext
    · simp only [Or.by_cases, dif_pos]
    · ext ⟨i, his⟩
      have : ¬i = a := by
        rintro rfl
        exact has his
      simp only [Or.by_cases, this, not_false_iff, dif_neg]
  · intro f
    ext ⟨i, hi⟩
    rcases Finset.mem_insert.1 hi with (rfl | h)
    · simp only [Or.by_cases, dif_pos]
    · have : ¬i = a := by
        rintro rfl
        exact has h
      simp only [Or.by_cases, dif_neg this, dif_pos h]
#align is_noetherian_pi isNoetherian_pi
-/

#print isNoetherian_pi' /-
/-- A version of `is_noetherian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance isNoetherian_pi' {R ι M : Type _} [Ring R] [AddCommGroup M] [Module R M] [Finite ι]
    [IsNoetherian R M] : IsNoetherian R (ι → M) :=
  isNoetherian_pi
#align is_noetherian_pi' isNoetherian_pi'
-/

end

open IsNoetherian Submodule Function

section

universe w

variable {R M P : Type _} {N : Type w} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid P] [Module R P]

/- warning: is_noetherian_iff_well_founded -> isNoetherian_iff_wellFounded is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2], Iff (IsNoetherian.{u1, u2} R M _inst_1 _inst_2 _inst_3) (WellFounded.{succ u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (GT.gt.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Preorder.toLT.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Submodule.completeLattice.{u1, u2} R M _inst_1 _inst_2 _inst_3)))))))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M _inst_1 _inst_2], Iff (IsNoetherian.{u2, u1} R M _inst_1 _inst_2 _inst_3) (WellFounded.{succ u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (fun (x._@.Mathlib.RingTheory.Noetherian._hyg.2248 : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (x._@.Mathlib.RingTheory.Noetherian._hyg.2250 : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) => GT.gt.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (Preorder.toLT.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (Submodule.completeLattice.{u2, u1} R M _inst_1 _inst_2 _inst_3))))) x._@.Mathlib.RingTheory.Noetherian._hyg.2248 x._@.Mathlib.RingTheory.Noetherian._hyg.2250))
Case conversion may be inaccurate. Consider using '#align is_noetherian_iff_well_founded isNoetherian_iff_wellFoundedₓ'. -/
theorem isNoetherian_iff_wellFounded :
    IsNoetherian R M ↔ WellFounded ((· > ·) : Submodule R M → Submodule R M → Prop) :=
  by
  rw [(CompleteLattice.wellFounded_characterisations <| Submodule R M).out 0 3]
  exact
    ⟨fun ⟨h⟩ => fun k => (fg_iff_compact k).mp (h k), fun h =>
      ⟨fun k => (fg_iff_compact k).mpr (h k)⟩⟩
#align is_noetherian_iff_well_founded isNoetherian_iff_wellFounded

/- warning: is_noetherian_iff_fg_well_founded -> isNoetherian_iff_fg_wellFounded is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2], Iff (IsNoetherian.{u1, u2} R M _inst_1 _inst_2 _inst_3) (WellFounded.{succ u2} (Subtype.{succ u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (fun (N : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) => Submodule.Fg.{u1, u2} R M _inst_1 _inst_2 _inst_3 N)) (GT.gt.{u2} (Subtype.{succ u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (fun (N : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) => Submodule.Fg.{u1, u2} R M _inst_1 _inst_2 _inst_3 N)) (Subtype.hasLt.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Preorder.toLT.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Submodule.completeLattice.{u1, u2} R M _inst_1 _inst_2 _inst_3))))) (fun (N : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) => Submodule.Fg.{u1, u2} R M _inst_1 _inst_2 _inst_3 N))))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M _inst_1 _inst_2], Iff (IsNoetherian.{u2, u1} R M _inst_1 _inst_2 _inst_3) (WellFounded.{succ u1} (Subtype.{succ u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (fun (N : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) => Submodule.Fg.{u2, u1} R M _inst_1 _inst_2 _inst_3 N)) (fun (x._@.Mathlib.RingTheory.Noetherian._hyg.2457 : Subtype.{succ u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (fun (N : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) => Submodule.Fg.{u2, u1} R M _inst_1 _inst_2 _inst_3 N)) (x._@.Mathlib.RingTheory.Noetherian._hyg.2459 : Subtype.{succ u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (fun (N : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) => Submodule.Fg.{u2, u1} R M _inst_1 _inst_2 _inst_3 N)) => GT.gt.{u1} (Subtype.{succ u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (fun (N : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) => Submodule.Fg.{u2, u1} R M _inst_1 _inst_2 _inst_3 N)) (Subtype.lt.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (Preorder.toLT.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (Submodule.completeLattice.{u2, u1} R M _inst_1 _inst_2 _inst_3))))) (fun (N : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) => Submodule.Fg.{u2, u1} R M _inst_1 _inst_2 _inst_3 N)) x._@.Mathlib.RingTheory.Noetherian._hyg.2457 x._@.Mathlib.RingTheory.Noetherian._hyg.2459))
Case conversion may be inaccurate. Consider using '#align is_noetherian_iff_fg_well_founded isNoetherian_iff_fg_wellFoundedₓ'. -/
theorem isNoetherian_iff_fg_wellFounded :
    IsNoetherian R M ↔
      WellFounded
        ((· > ·) : { N : Submodule R M // N.Fg } → { N : Submodule R M // N.Fg } → Prop) :=
  by
  let α := { N : Submodule R M // N.Fg }
  constructor
  · intro H
    let f : α ↪o Submodule R M := OrderEmbedding.subtype _
    exact OrderEmbedding.wellFounded f.dual (is_noetherian_iff_well_founded.mp H)
  · intro H
    constructor
    intro N
    obtain ⟨⟨N₀, h₁⟩, e : N₀ ≤ N, h₂⟩ :=
      WellFounded.has_min H { N' : α | N'.1 ≤ N } ⟨⟨⊥, Submodule.fg_bot⟩, bot_le⟩
    convert h₁
    refine' (e.antisymm _).symm
    by_contra h₃
    obtain ⟨x, hx₁ : x ∈ N, hx₂ : x ∉ N₀⟩ := set.not_subset.mp h₃
    apply hx₂
    have := eq_of_le_of_not_lt _ (h₂ ⟨(R ∙ x) ⊔ N₀, _⟩ _)
    · injection this with eq
      rw [Eq]
      exact (le_sup_left : (R ∙ x) ≤ (R ∙ x) ⊔ N₀) (Submodule.mem_span_singleton_self _)
    · exact Submodule.Fg.sup ⟨{x}, by rw [Finset.coe_singleton]⟩ h₁
    · show N₀ ≤ (R ∙ x) ⊔ N₀
      exact le_sup_right
    · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₁) e
#align is_noetherian_iff_fg_well_founded isNoetherian_iff_fg_wellFounded

variable (R M)

/- warning: well_founded_submodule_gt -> wellFounded_submodule_gt is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_8 : Semiring.{u1} R] [_inst_9 : AddCommMonoid.{u2} M] [_inst_10 : Module.{u1, u2} R M _inst_8 _inst_9] [_inst_11 : IsNoetherian.{u1, u2} R M _inst_8 _inst_9 _inst_10], WellFounded.{succ u2} (Submodule.{u1, u2} R M _inst_8 _inst_9 _inst_10) (GT.gt.{u2} (Submodule.{u1, u2} R M _inst_8 _inst_9 _inst_10) (Preorder.toLT.{u2} (Submodule.{u1, u2} R M _inst_8 _inst_9 _inst_10) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M _inst_8 _inst_9 _inst_10) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submodule.{u1, u2} R M _inst_8 _inst_9 _inst_10) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submodule.{u1, u2} R M _inst_8 _inst_9 _inst_10) (Submodule.completeLattice.{u1, u2} R M _inst_8 _inst_9 _inst_10))))))
but is expected to have type
  forall (R : Type.{u2}) (M : Type.{u1}) [_inst_8 : Semiring.{u2} R] [_inst_9 : AddCommMonoid.{u1} M] [_inst_10 : Module.{u2, u1} R M _inst_8 _inst_9] [_inst_11 : IsNoetherian.{u2, u1} R M _inst_8 _inst_9 _inst_10], WellFounded.{succ u1} (Submodule.{u2, u1} R M _inst_8 _inst_9 _inst_10) (fun (x._@.Mathlib.RingTheory.Noetherian._hyg.2852 : Submodule.{u2, u1} R M _inst_8 _inst_9 _inst_10) (x._@.Mathlib.RingTheory.Noetherian._hyg.2854 : Submodule.{u2, u1} R M _inst_8 _inst_9 _inst_10) => GT.gt.{u1} (Submodule.{u2, u1} R M _inst_8 _inst_9 _inst_10) (Preorder.toLT.{u1} (Submodule.{u2, u1} R M _inst_8 _inst_9 _inst_10) (PartialOrder.toPreorder.{u1} (Submodule.{u2, u1} R M _inst_8 _inst_9 _inst_10) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Submodule.{u2, u1} R M _inst_8 _inst_9 _inst_10) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Submodule.{u2, u1} R M _inst_8 _inst_9 _inst_10) (Submodule.completeLattice.{u2, u1} R M _inst_8 _inst_9 _inst_10))))) x._@.Mathlib.RingTheory.Noetherian._hyg.2852 x._@.Mathlib.RingTheory.Noetherian._hyg.2854)
Case conversion may be inaccurate. Consider using '#align well_founded_submodule_gt wellFounded_submodule_gtₓ'. -/
theorem wellFounded_submodule_gt (R M) [Semiring R] [AddCommMonoid M] [Module R M] :
    ∀ [IsNoetherian R M], WellFounded ((· > ·) : Submodule R M → Submodule R M → Prop) :=
  isNoetherian_iff_wellFounded.mp
#align well_founded_submodule_gt wellFounded_submodule_gt

variable {R M}

/- warning: set_has_maximal_iff_noetherian -> set_has_maximal_iff_noetherian is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2], Iff (forall (a : Set.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3)), (Set.Nonempty.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) a) -> (Exists.{succ u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (fun (M' : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) => Exists.{0} (Membership.Mem.{u2, u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Set.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3)) (Set.hasMem.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3)) M' a) (fun (H : Membership.Mem.{u2, u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Set.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3)) (Set.hasMem.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3)) M' a) => forall (I : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3), (Membership.Mem.{u2, u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Set.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3)) (Set.hasMem.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3)) I a) -> (Not (LT.lt.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Preorder.toLT.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Submodule.completeLattice.{u1, u2} R M _inst_1 _inst_2 _inst_3))))) M' I)))))) (IsNoetherian.{u1, u2} R M _inst_1 _inst_2 _inst_3)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2], Iff (forall (a : Set.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3)), (Set.Nonempty.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) a) -> (Exists.{succ u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (fun (M' : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) => And (Membership.mem.{u2, u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Set.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3)) (Set.instMembershipSet.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3)) M' a) (forall (I : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3), (Membership.mem.{u2, u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Set.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3)) (Set.instMembershipSet.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3)) I a) -> (Not (LT.lt.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Preorder.toLT.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Submodule.completeLattice.{u1, u2} R M _inst_1 _inst_2 _inst_3))))) M' I)))))) (IsNoetherian.{u1, u2} R M _inst_1 _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align set_has_maximal_iff_noetherian set_has_maximal_iff_noetherianₓ'. -/
/-- A module is Noetherian iff every nonempty set of submodules has a maximal submodule among them.
-/
theorem set_has_maximal_iff_noetherian :
    (∀ a : Set <| Submodule R M, a.Nonempty → ∃ M' ∈ a, ∀ I ∈ a, ¬M' < I) ↔ IsNoetherian R M := by
  rw [isNoetherian_iff_wellFounded, WellFounded.wellFounded_iff_has_min]
#align set_has_maximal_iff_noetherian set_has_maximal_iff_noetherian

#print monotone_stabilizes_iff_noetherian /-
/-- A module is Noetherian iff every increasing chain of submodules stabilizes. -/
theorem monotone_stabilizes_iff_noetherian :
    (∀ f : ℕ →o Submodule R M, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsNoetherian R M := by
  rw [isNoetherian_iff_wellFounded, WellFounded.monotone_chain_condition]
#align monotone_stabilizes_iff_noetherian monotone_stabilizes_iff_noetherian
-/

/- warning: is_noetherian.induction -> IsNoetherian.induction is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_8 : IsNoetherian.{u1, u2} R M _inst_1 _inst_2 _inst_3] {P : (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) -> Prop}, (forall (I : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3), (forall (J : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3), (GT.gt.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Preorder.toLT.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Submodule.completeLattice.{u1, u2} R M _inst_1 _inst_2 _inst_3))))) J I) -> (P J)) -> (P I)) -> (forall (I : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3), P I)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M _inst_1 _inst_2] [_inst_8 : IsNoetherian.{u2, u1} R M _inst_1 _inst_2 _inst_3] {P : (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) -> Prop}, (forall (I : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3), (forall (J : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3), (GT.gt.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (Preorder.toLT.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (Submodule.completeLattice.{u2, u1} R M _inst_1 _inst_2 _inst_3))))) J I) -> (P J)) -> (P I)) -> (forall (I : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3), P I)
Case conversion may be inaccurate. Consider using '#align is_noetherian.induction IsNoetherian.inductionₓ'. -/
/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
theorem IsNoetherian.induction [IsNoetherian R M] {P : Submodule R M → Prop}
    (hgt : ∀ I, (∀ J > I, P J) → P I) (I : Submodule R M) : P I :=
  WellFounded.recursion (wellFounded_submodule_gt R M) I hgt
#align is_noetherian.induction IsNoetherian.induction

end

section

universe w

variable {R M P : Type _} {N : Type w} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P]

/- warning: finite_of_linear_independent -> finite_of_linearIndependent is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_8 : Nontrivial.{u1} R] [_inst_9 : IsNoetherian.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3] {s : Set.{u2} M}, (LinearIndependent.{u2, u1, u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} M) Type.{u2} (Set.hasCoeToSort.{u2} M) s) R M ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} M) Type.{u2} (Set.hasCoeToSort.{u2} M) s) M (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} M) Type.{u2} (Set.hasCoeToSort.{u2} M) s) M (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} M) Type.{u2} (Set.hasCoeToSort.{u2} M) s) M (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} M) Type.{u2} (Set.hasCoeToSort.{u2} M) s) M (coeSubtype.{succ u2} M (fun (x : M) => Membership.Mem.{u2, u2} M (Set.{u2} M) (Set.hasMem.{u2} M) x s)))))) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) -> (Set.Finite.{u2} M s)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] [_inst_8 : Nontrivial.{u2} R] [_inst_9 : IsNoetherian.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3] {s : Set.{u1} M}, (LinearIndependent.{u1, u2, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x s)) R M (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x s)) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) -> (Set.Finite.{u1} M s)
Case conversion may be inaccurate. Consider using '#align finite_of_linear_independent finite_of_linearIndependentₓ'. -/
theorem finite_of_linearIndependent [Nontrivial R] [IsNoetherian R M] {s : Set M}
    (hs : LinearIndependent R (coe : s → M)) : s.Finite :=
  by
  refine'
    by_contradiction fun hf =>
      (RelEmbedding.wellFounded_iff_no_descending_seq.1 (wellFounded_submodule_gt R M)).elim' _
  have f : ℕ ↪ s := Set.Infinite.natEmbedding s hf
  have : ∀ n, coe ∘ f '' { m | m ≤ n } ⊆ s :=
    by
    rintro n x ⟨y, hy₁, rfl⟩
    exact (f y).2
  have : ∀ a b : ℕ, a ≤ b ↔ span R (coe ∘ f '' { m | m ≤ a }) ≤ span R (coe ∘ f '' { m | m ≤ b }) :=
    by
    intro a b
    rw [span_le_span_iff hs (this a) (this b),
      Set.image_subset_image_iff (subtype.coe_injective.comp f.injective), Set.subset_def]
    exact ⟨fun hab x (hxa : x ≤ a) => le_trans hxa hab, fun hx => hx a (le_refl a)⟩
  exact
    ⟨⟨fun n => span R (coe ∘ f '' { m | m ≤ n }), fun x y => by
        simp (config := { contextual := true }) [le_antisymm_iff, (this _ _).symm]⟩,
      by dsimp [GT.gt] <;> simp only [lt_iff_le_not_le, (this _ _).symm] <;> tauto⟩
#align finite_of_linear_independent finite_of_linearIndependent

/- warning: is_noetherian_of_range_eq_ker -> isNoetherian_of_range_eq_ker is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u2}} {M : Type.{u3}} {P : Type.{u4}} {N : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u3} M] [_inst_3 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2)] [_inst_4 : AddCommGroup.{u1} N] [_inst_5 : Module.{u2, u1} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4)] [_inst_6 : AddCommGroup.{u4} P] [_inst_7 : Module.{u2, u4} R P (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} P _inst_6)] [_inst_8 : IsNoetherian.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) _inst_3] [_inst_9 : IsNoetherian.{u2, u4} R P (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} P _inst_6) _inst_7] (f : LinearMap.{u2, u2, u3, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M N (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_3 _inst_5) (g : LinearMap.{u2, u2, u1, u4} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) N P (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) (AddCommGroup.toAddCommMonoid.{u4} P _inst_6) _inst_5 _inst_7), (Function.Injective.{succ u3, succ u1} M N (coeFn.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (LinearMap.{u2, u2, u3, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M N (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_3 _inst_5) (fun (_x : LinearMap.{u2, u2, u3, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M N (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_3 _inst_5) => M -> N) (LinearMap.hasCoeToFun.{u2, u2, u3, u1} R R M N (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_3 _inst_5 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) f)) -> (Function.Surjective.{succ u1, succ u4} N P (coeFn.{max (succ u1) (succ u4), max (succ u1) (succ u4)} (LinearMap.{u2, u2, u1, u4} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) N P (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) (AddCommGroup.toAddCommMonoid.{u4} P _inst_6) _inst_5 _inst_7) (fun (_x : LinearMap.{u2, u2, u1, u4} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) N P (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) (AddCommGroup.toAddCommMonoid.{u4} P _inst_6) _inst_5 _inst_7) => N -> P) (LinearMap.hasCoeToFun.{u2, u2, u1, u4} R R N P (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) (AddCommGroup.toAddCommMonoid.{u4} P _inst_6) _inst_5 _inst_7 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) g)) -> (Eq.{succ u1} (Submodule.{u2, u1} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_5) (LinearMap.range.{u2, u2, u3, u1, max u3 u1} R R M N (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_3 _inst_5 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (LinearMap.{u2, u2, u3, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M N (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_3 _inst_5) (LinearMap.semilinearMapClass.{u2, u2, u3, u1} R R M N (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_3 _inst_5 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (RingHomSurjective.ids.{u2} R (Ring.toSemiring.{u2} R _inst_1)) f) (LinearMap.ker.{u2, u2, u1, u4, max u1 u4} R R N P (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) (AddCommGroup.toAddCommMonoid.{u4} P _inst_6) _inst_5 _inst_7 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (LinearMap.{u2, u2, u1, u4} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) N P (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) (AddCommGroup.toAddCommMonoid.{u4} P _inst_6) _inst_5 _inst_7) (LinearMap.semilinearMapClass.{u2, u2, u1, u4} R R N P (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) (AddCommGroup.toAddCommMonoid.{u4} P _inst_6) _inst_5 _inst_7 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) g)) -> (IsNoetherian.{u2, u1} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_5)
but is expected to have type
  forall {R : Type.{u3}} {M : Type.{u2}} {P : Type.{u1}} {N : Type.{u4}} [_inst_1 : Ring.{u3} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_4 : AddCommGroup.{u4} N] [_inst_5 : Module.{u3, u4} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} N _inst_4)] [_inst_6 : AddCommGroup.{u1} P] [_inst_7 : Module.{u3, u1} R P (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} P _inst_6)] [_inst_8 : IsNoetherian.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3] [_inst_9 : IsNoetherian.{u3, u1} R P (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} P _inst_6) _inst_7] (f : LinearMap.{u3, u3, u2, u4} R R (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1))) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} N _inst_4) _inst_3 _inst_5) (g : LinearMap.{u3, u3, u4, u1} R R (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1))) N P (AddCommGroup.toAddCommMonoid.{u4} N _inst_4) (AddCommGroup.toAddCommMonoid.{u1} P _inst_6) _inst_5 _inst_7), (Function.Injective.{succ u2, succ u4} M N (FunLike.coe.{max (succ u4) (succ u2), succ u2, succ u4} (LinearMap.{u3, u3, u2, u4} R R (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1))) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} N _inst_4) _inst_3 _inst_5) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : M) => N) _x) (LinearMap.instFunLikeLinearMap.{u3, u3, u2, u4} R R M N (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} N _inst_4) _inst_3 _inst_5 (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1)))) f)) -> (Function.Surjective.{succ u4, succ u1} N P (FunLike.coe.{max (succ u4) (succ u1), succ u4, succ u1} (LinearMap.{u3, u3, u4, u1} R R (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1))) N P (AddCommGroup.toAddCommMonoid.{u4} N _inst_4) (AddCommGroup.toAddCommMonoid.{u1} P _inst_6) _inst_5 _inst_7) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : N) => P) _x) (LinearMap.instFunLikeLinearMap.{u3, u3, u4, u1} R R N P (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} N _inst_4) (AddCommGroup.toAddCommMonoid.{u1} P _inst_6) _inst_5 _inst_7 (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1)))) g)) -> (Eq.{succ u4} (Submodule.{u3, u4} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} N _inst_4) _inst_5) (LinearMap.range.{u3, u3, u2, u4, max u4 u2} R R M N (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} N _inst_4) _inst_3 _inst_5 (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1))) (LinearMap.{u3, u3, u2, u4} R R (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1))) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} N _inst_4) _inst_3 _inst_5) (LinearMap.instSemilinearMapClassLinearMap.{u3, u3, u2, u4} R R M N (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} N _inst_4) _inst_3 _inst_5 (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1)))) (RingHomSurjective.ids.{u3} R (Ring.toSemiring.{u3} R _inst_1)) f) (LinearMap.ker.{u3, u3, u4, u1, max u4 u1} R R N P (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} N _inst_4) (AddCommGroup.toAddCommMonoid.{u1} P _inst_6) _inst_5 _inst_7 (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1))) (LinearMap.{u3, u3, u4, u1} R R (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1))) N P (AddCommGroup.toAddCommMonoid.{u4} N _inst_4) (AddCommGroup.toAddCommMonoid.{u1} P _inst_6) _inst_5 _inst_7) (LinearMap.instSemilinearMapClassLinearMap.{u3, u3, u4, u1} R R N P (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} N _inst_4) (AddCommGroup.toAddCommMonoid.{u1} P _inst_6) _inst_5 _inst_7 (RingHom.id.{u3} R (NonAssocRing.toNonAssocSemiring.{u3} R (Ring.toNonAssocRing.{u3} R _inst_1)))) g)) -> (IsNoetherian.{u3, u4} R N (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} N _inst_4) _inst_5)
Case conversion may be inaccurate. Consider using '#align is_noetherian_of_range_eq_ker isNoetherian_of_range_eq_kerₓ'. -/
/-- If the first and final modules in a short exact sequence are noetherian,
  then the middle module is also noetherian. -/
theorem isNoetherian_of_range_eq_ker [IsNoetherian R M] [IsNoetherian R P] (f : M →ₗ[R] N)
    (g : N →ₗ[R] P) (hf : Function.Injective f) (hg : Function.Surjective g) (h : f.range = g.ker) :
    IsNoetherian R N :=
  isNoetherian_iff_wellFounded.2 <|
    wellFounded_gt_exact_sequence (wellFounded_submodule_gt R M) (wellFounded_submodule_gt R P)
      f.range (Submodule.map f) (Submodule.comap f) (Submodule.comap g) (Submodule.map g)
      (Submodule.gciMapComap hf) (Submodule.giMapComap hg)
      (by simp [Submodule.map_comap_eq, inf_comm]) (by simp [Submodule.comap_map_eq, h])
#align is_noetherian_of_range_eq_ker isNoetherian_of_range_eq_ker

/- warning: is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot -> IsNoetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [I : IsNoetherian.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3] (f : LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3), Exists.{1} Nat (fun (n : Nat) => And (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Eq.{succ u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Inf.inf.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasInf.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (LinearMap.ker.{u1, u1, u2, u2, u2} R R M M (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) (LinearMap.semilinearMapClass.{u1, u1, u2, u2} R R M M (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (HPow.hPow.{u2, 0, u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) Nat (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) (instHPow.{u2, 0} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) Nat (Monoid.Pow.{u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) (Module.End.monoid.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))) f n)) (LinearMap.range.{u1, u1, u2, u2, u2} R R M M (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) (LinearMap.semilinearMapClass.{u1, u1, u2, u2} R R M M (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (RingHomSurjective.ids.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (HPow.hPow.{u2, 0, u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) Nat (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) (instHPow.{u2, 0} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) Nat (Monoid.Pow.{u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) (Module.End.monoid.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))) f n))) (Bot.bot.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasBot.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] [I : IsNoetherian.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3] (f : LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3), Exists.{1} Nat (fun (n : Nat) => And (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Eq.{succ u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Inf.inf.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.instInfSubmodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (LinearMap.ker.{u2, u2, u1, u1, u1} R R M M (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3) (LinearMap.instSemilinearMapClassLinearMap.{u2, u2, u1, u1} R R M M (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (HPow.hPow.{u1, 0, u1} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3) Nat (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3) (instHPow.{u1, 0} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3) Nat (Monoid.Pow.{u1} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3) (Module.End.monoid.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3))) f n)) (LinearMap.range.{u2, u2, u1, u1, u1} R R M M (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3) (LinearMap.instSemilinearMapClassLinearMap.{u2, u2, u1, u1} R R M M (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (RingHomSurjective.ids.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (HPow.hPow.{u1, 0, u1} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3) Nat (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3) (instHPow.{u1, 0} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3) Nat (Monoid.Pow.{u1} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3) (Module.End.monoid.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3))) f n))) (Bot.bot.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.instBotSubmodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3))))
Case conversion may be inaccurate. Consider using '#align is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot IsNoetherian.exists_endomorphism_iterate_ker_inf_range_eq_botₓ'. -/
/-- For any endomorphism of a Noetherian module, there is some nontrivial iterate
with disjoint kernel and range.
-/
theorem IsNoetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot [I : IsNoetherian R M]
    (f : M →ₗ[R] M) : ∃ n : ℕ, n ≠ 0 ∧ (f ^ n).ker ⊓ (f ^ n).range = ⊥ :=
  by
  obtain ⟨n, w⟩ :=
    monotone_stabilizes_iff_noetherian.mpr I
      (f.iterate_ker.comp ⟨fun n => n + 1, fun n m w => by linarith⟩)
  specialize w (2 * n + 1) (by linarith only)
  dsimp at w
  refine' ⟨n + 1, Nat.succ_ne_zero _, _⟩
  rw [eq_bot_iff]
  rintro - ⟨h, ⟨y, rfl⟩⟩
  rw [mem_bot, ← LinearMap.mem_ker, w]
  erw [LinearMap.mem_ker] at h⊢
  change (f ^ (n + 1) * f ^ (n + 1)) y = 0 at h
  rw [← pow_add] at h
  convert h using 3
  ring
#align is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot IsNoetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot

/- warning: is_noetherian.injective_of_surjective_endomorphism -> IsNoetherian.injective_of_surjective_endomorphism is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_8 : IsNoetherian.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3] (f : LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3), (Function.Surjective.{succ u2, succ u2} M M (coeFn.{succ u2, succ u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) (fun (_x : LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) => M -> M) (LinearMap.hasCoeToFun.{u1, u1, u2, u2} R R M M (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) f)) -> (Function.Injective.{succ u2, succ u2} M M (coeFn.{succ u2, succ u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) (fun (_x : LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) => M -> M) (LinearMap.hasCoeToFun.{u1, u1, u2, u2} R R M M (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) f))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] [_inst_8 : IsNoetherian.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3] (f : LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3), (Function.Surjective.{succ u1, succ u1} M M (FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : M) => M) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u1, u1} R R M M (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) f)) -> (Function.Injective.{succ u1, succ u1} M M (FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : M) => M) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u1, u1} R R M M (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) f))
Case conversion may be inaccurate. Consider using '#align is_noetherian.injective_of_surjective_endomorphism IsNoetherian.injective_of_surjective_endomorphismₓ'. -/
/-- Any surjective endomorphism of a Noetherian module is injective. -/
theorem IsNoetherian.injective_of_surjective_endomorphism [IsNoetherian R M] (f : M →ₗ[R] M)
    (s : Surjective f) : Injective f :=
  by
  obtain ⟨n, ne, w⟩ := IsNoetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot f
  rw [linear_map.range_eq_top.mpr (LinearMap.iterate_surjective s n), inf_top_eq,
    LinearMap.ker_eq_bot] at w
  exact LinearMap.injective_of_iterate_injective Ne w
#align is_noetherian.injective_of_surjective_endomorphism IsNoetherian.injective_of_surjective_endomorphism

/- warning: is_noetherian.bijective_of_surjective_endomorphism -> IsNoetherian.bijective_of_surjective_endomorphism is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_8 : IsNoetherian.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3] (f : LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3), (Function.Surjective.{succ u2, succ u2} M M (coeFn.{succ u2, succ u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) (fun (_x : LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) => M -> M) (LinearMap.hasCoeToFun.{u1, u1, u2, u2} R R M M (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) f)) -> (Function.Bijective.{succ u2, succ u2} M M (coeFn.{succ u2, succ u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) (fun (_x : LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3) => M -> M) (LinearMap.hasCoeToFun.{u1, u1, u2, u2} R R M M (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) f))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] [_inst_8 : IsNoetherian.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3] (f : LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3), (Function.Surjective.{succ u1, succ u1} M M (FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : M) => M) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u1, u1} R R M M (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) f)) -> (Function.Bijective.{succ u1, succ u1} M M (FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : M) => M) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u1, u1} R R M M (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) f))
Case conversion may be inaccurate. Consider using '#align is_noetherian.bijective_of_surjective_endomorphism IsNoetherian.bijective_of_surjective_endomorphismₓ'. -/
/-- Any surjective endomorphism of a Noetherian module is bijective. -/
theorem IsNoetherian.bijective_of_surjective_endomorphism [IsNoetherian R M] (f : M →ₗ[R] M)
    (s : Surjective f) : Bijective f :=
  ⟨IsNoetherian.injective_of_surjective_endomorphism f s, s⟩
#align is_noetherian.bijective_of_surjective_endomorphism IsNoetherian.bijective_of_surjective_endomorphism

/- warning: is_noetherian.disjoint_partial_sups_eventually_bot -> IsNoetherian.disjoint_partialSups_eventually_bot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [I : IsNoetherian.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3] (f : Nat -> (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)), (forall (n : Nat), Disjoint.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.completeLattice.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))) (Submodule.orderBot.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (coeFn.{succ u2, succ u2} (OrderHom.{0, u2} Nat (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SemilatticeSup.toPartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Lattice.toSemilatticeSup.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (ConditionallyCompleteLattice.toLattice.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.completeLattice.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))))) (fun (_x : OrderHom.{0, u2} Nat (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SemilatticeSup.toPartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Lattice.toSemilatticeSup.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (ConditionallyCompleteLattice.toLattice.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.completeLattice.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))))) => Nat -> (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) (OrderHom.hasCoeToFun.{0, u2} Nat (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SemilatticeSup.toPartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Lattice.toSemilatticeSup.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (ConditionallyCompleteLattice.toLattice.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.completeLattice.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))))) (partialSups.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Lattice.toSemilatticeSup.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (ConditionallyCompleteLattice.toLattice.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.completeLattice.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) f) n) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) -> (Exists.{1} Nat (fun (n : Nat) => forall (m : Nat), (LE.le.{0} Nat Nat.hasLe n m) -> (Eq.{succ u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (f m) (Bot.bot.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasBot.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] [I : IsNoetherian.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3] (f : Nat -> (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3)), (forall (n : Nat), Disjoint.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.completeLattice.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3))) (Submodule.instOrderBotSubmoduleToLEToPreorderInstPartialOrderSetLike.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (OrderHom.toFun.{0, u1} Nat (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (SemilatticeSup.toPartialOrder.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Lattice.toSemilatticeSup.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (ConditionallyCompleteLattice.toLattice.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.completeLattice.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3)))))) (partialSups.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Lattice.toSemilatticeSup.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (ConditionallyCompleteLattice.toLattice.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.completeLattice.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3)))) f) n) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) -> (Exists.{1} Nat (fun (n : Nat) => forall (m : Nat), (LE.le.{0} Nat instLENat n m) -> (Eq.{succ u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (f m) (Bot.bot.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.instBotSubmodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3)))))
Case conversion may be inaccurate. Consider using '#align is_noetherian.disjoint_partial_sups_eventually_bot IsNoetherian.disjoint_partialSups_eventually_botₓ'. -/
/-- A sequence `f` of submodules of a noetherian module,
with `f (n+1)` disjoint from the supremum of `f 0`, ..., `f n`,
is eventually zero.
-/
theorem IsNoetherian.disjoint_partialSups_eventually_bot [I : IsNoetherian R M]
    (f : ℕ → Submodule R M) (h : ∀ n, Disjoint (partialSups f n) (f (n + 1))) :
    ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊥ :=
  by
  -- A little off-by-one cleanup first:
  suffices t : ∃ n : ℕ, ∀ m, n ≤ m → f (m + 1) = ⊥
  · obtain ⟨n, w⟩ := t
    use n + 1
    rintro (_ | m) p
    · cases p
    · apply w
      exact nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr I (partialSups f)
  exact
    ⟨n, fun m p =>
      (h m).eq_bot_of_ge <| sup_eq_left.1 <| (w (m + 1) <| le_add_right p).symm.trans <| w m p⟩
#align is_noetherian.disjoint_partial_sups_eventually_bot IsNoetherian.disjoint_partialSups_eventually_bot

/- warning: is_noetherian.equiv_punit_of_prod_injective -> IsNoetherian.equivPunitOfProdInjective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u2}} {M : Type.{u3}} {N : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u3} M] [_inst_3 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2)] [_inst_4 : AddCommGroup.{u1} N] [_inst_5 : Module.{u2, u1} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4)] [_inst_8 : IsNoetherian.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) _inst_3] (f : LinearMap.{u2, u2, max u3 u1, u3} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (Prod.{u3, u1} M N) M (Prod.addCommMonoid.{u3, u1} M N (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (Prod.module.{u2, u3, u1} R M N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_3 _inst_5) _inst_3), (Function.Injective.{max (succ u3) (succ u1), succ u3} (Prod.{u3, u1} M N) M (coeFn.{max (succ (max u3 u1)) (succ u3), max (succ (max u3 u1)) (succ u3)} (LinearMap.{u2, u2, max u3 u1, u3} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (Prod.{u3, u1} M N) M (Prod.addCommMonoid.{u3, u1} M N (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (Prod.module.{u2, u3, u1} R M N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_3 _inst_5) _inst_3) (fun (_x : LinearMap.{u2, u2, max u3 u1, u3} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (Prod.{u3, u1} M N) M (Prod.addCommMonoid.{u3, u1} M N (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (Prod.module.{u2, u3, u1} R M N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_3 _inst_5) _inst_3) => (Prod.{u3, u1} M N) -> M) (LinearMap.hasCoeToFun.{u2, u2, max u3 u1, u3} R R (Prod.{u3, u1} M N) M (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (Prod.addCommMonoid.{u3, u1} M N (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (Prod.module.{u2, u3, u1} R M N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_3 _inst_5) _inst_3 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) f)) -> (LinearEquiv.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (IsNoetherian.equivPunitOfProdInjective._proof_1.{u2} R _inst_1) (IsNoetherian.equivPunitOfProdInjective._proof_2.{u2} R _inst_1) N PUnit.{succ u1} (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) (AddCommGroup.toAddCommMonoid.{u1} PUnit.{succ u1} PUnit.addCommGroup.{u1}) _inst_5 (PUnit.module.{u2, u1} R (Ring.toSemiring.{u2} R _inst_1)))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u3}} {N : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u3} M] [_inst_3 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2)] [_inst_4 : AddCommGroup.{u1} N] [_inst_5 : Module.{u2, u1} R N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4)] [_inst_8 : IsNoetherian.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) _inst_3] (f : LinearMap.{u2, u2, max u1 u3, u3} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (Prod.{u3, u1} M N) M (Prod.instAddCommMonoidSum.{u3, u1} M N (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (Prod.module.{u2, u3, u1} R M N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_3 _inst_5) _inst_3), (Function.Injective.{max (succ u1) (succ u3), succ u3} (Prod.{u3, u1} M N) M (FunLike.coe.{max (succ u1) (succ u3), max (succ u1) (succ u3), succ u3} (LinearMap.{u2, u2, max u1 u3, u3} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (Prod.{u3, u1} M N) M (Prod.instAddCommMonoidSum.{u3, u1} M N (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (Prod.module.{u2, u3, u1} R M N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_3 _inst_5) _inst_3) (Prod.{u3, u1} M N) (fun (_x : Prod.{u3, u1} M N) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : Prod.{u3, u1} M N) => M) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, max u1 u3, u3} R R (Prod.{u3, u1} M N) M (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (Prod.instAddCommMonoidSum.{u3, u1} M N (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (Prod.module.{u2, u3, u1} R M N (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) _inst_3 _inst_5) _inst_3 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) f)) -> (LinearEquiv.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (RingHomInvPair.ids.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (RingHomInvPair.ids.{u2} R (Ring.toSemiring.{u2} R _inst_1)) N PUnit.{succ u1} (AddCommGroup.toAddCommMonoid.{u1} N _inst_4) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} PUnit.{succ u1} (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u1} PUnit.{succ u1} PUnit.linearOrderedCancelAddCommMonoid.{u1})) _inst_5 (PUnit.module.{u2, u1} R (Ring.toSemiring.{u2} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_noetherian.equiv_punit_of_prod_injective IsNoetherian.equivPunitOfProdInjectiveₓ'. -/
/-- If `M ⊕ N` embeds into `M`, for `M` noetherian over `R`, then `N` is trivial.
-/
noncomputable def IsNoetherian.equivPunitOfProdInjective [IsNoetherian R M] (f : M × N →ₗ[R] M)
    (i : Injective f) : N ≃ₗ[R] PUnit.{w + 1} :=
  by
  apply Nonempty.some
  obtain ⟨n, w⟩ :=
    IsNoetherian.disjoint_partialSups_eventually_bot (f.tailing i) (f.tailings_disjoint_tailing i)
  specialize w n (le_refl n)
  apply Nonempty.intro
  refine' (f.tailing_linear_equiv i n).symm ≪≫ₗ _
  rw [w]
  exact Submodule.botEquivPUnit
#align is_noetherian.equiv_punit_of_prod_injective IsNoetherian.equivPunitOfProdInjective

end

#print IsNoetherianRing /-
/-- A (semi)ring is Noetherian if it is Noetherian as a module over itself,
i.e. all its ideals are finitely generated.
-/
@[reducible]
def IsNoetherianRing (R) [Semiring R] :=
  IsNoetherian R R
#align is_noetherian_ring IsNoetherianRing
-/

#print isNoetherianRing_iff /-
theorem isNoetherianRing_iff {R} [Semiring R] : IsNoetherianRing R ↔ IsNoetherian R R :=
  Iff.rfl
#align is_noetherian_ring_iff isNoetherianRing_iff
-/

#print isNoetherianRing_iff_ideal_fg /-
/-- A ring is Noetherian if and only if all its ideals are finitely-generated. -/
theorem isNoetherianRing_iff_ideal_fg (R : Type _) [Semiring R] :
    IsNoetherianRing R ↔ ∀ I : Ideal R, I.Fg :=
  isNoetherianRing_iff.trans isNoetherian_def
#align is_noetherian_ring_iff_ideal_fg isNoetherianRing_iff_ideal_fg
-/

#print isNoetherian_of_finite /-
-- see Note [lower instance priority]
instance (priority := 80) isNoetherian_of_finite (R M) [Finite M] [Semiring R] [AddCommMonoid M]
    [Module R M] : IsNoetherian R M :=
  ⟨fun s => ⟨(s : Set M).toFinite.toFinset, by rw [Set.Finite.coe_toFinset, Submodule.span_eq]⟩⟩
#align is_noetherian_of_finite isNoetherian_of_finite
-/

#print isNoetherian_of_subsingleton /-
-- see Note [lower instance priority]
/-- Modules over the trivial ring are Noetherian. -/
instance (priority := 100) isNoetherian_of_subsingleton (R M) [Subsingleton R] [Semiring R]
    [AddCommMonoid M] [Module R M] : IsNoetherian R M :=
  haveI := Module.subsingleton R M
  isNoetherian_of_finite R M
#align is_noetherian_of_subsingleton isNoetherian_of_subsingleton
-/

/- warning: is_noetherian_of_submodule_of_noetherian -> isNoetherian_of_submodule_of_noetherian is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2] (N : Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3), (IsNoetherian.{u1, u2} R M _inst_1 _inst_2 _inst_3) -> (IsNoetherian.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submodule.{u1, u2} R M _inst_1 _inst_2 _inst_3) M (Submodule.setLike.{u1, u2} R M _inst_1 _inst_2 _inst_3)) N) _inst_1 (Submodule.addCommMonoid.{u1, u2} R M _inst_1 _inst_2 _inst_3 N) (Submodule.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 N))
but is expected to have type
  forall (R : Type.{u2}) (M : Type.{u1}) [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M _inst_1 _inst_2] (N : Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3), (IsNoetherian.{u2, u1} R M _inst_1 _inst_2 _inst_3) -> (IsNoetherian.{u2, u1} R (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} R M _inst_1 _inst_2 _inst_3) M (Submodule.setLike.{u2, u1} R M _inst_1 _inst_2 _inst_3)) x N)) _inst_1 (Submodule.addCommMonoid.{u2, u1} R M _inst_1 _inst_2 _inst_3 N) (Submodule.module.{u2, u1} R M _inst_1 _inst_2 _inst_3 N))
Case conversion may be inaccurate. Consider using '#align is_noetherian_of_submodule_of_noetherian isNoetherian_of_submodule_of_noetherianₓ'. -/
theorem isNoetherian_of_submodule_of_noetherian (R M) [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) (h : IsNoetherian R M) : IsNoetherian R N :=
  by
  rw [isNoetherian_iff_wellFounded] at h⊢
  exact OrderEmbedding.wellFounded (Submodule.MapSubtype.orderEmbedding N).dual h
#align is_noetherian_of_submodule_of_noetherian isNoetherian_of_submodule_of_noetherian

#print Submodule.Quotient.isNoetherian /-
instance Submodule.Quotient.isNoetherian {R} [Ring R] {M} [AddCommGroup M] [Module R M]
    (N : Submodule R M) [h : IsNoetherian R M] : IsNoetherian R (M ⧸ N) :=
  by
  rw [isNoetherian_iff_wellFounded] at h⊢
  exact OrderEmbedding.wellFounded (Submodule.comapMkQOrderEmbedding N).dual h
#align submodule.quotient.is_noetherian Submodule.Quotient.isNoetherian
-/

/- warning: is_noetherian_of_tower -> isNoetherian_of_tower is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {S : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] [_inst_3 : AddCommMonoid.{u3} M] [_inst_4 : SMul.{u1, u2} R S] [_inst_5 : Module.{u2, u3} S M _inst_2 _inst_3] [_inst_6 : Module.{u1, u3} R M _inst_1 _inst_3] [_inst_7 : IsScalarTower.{u1, u2, u3} R S M _inst_4 (SMulZeroClass.toHasSmul.{u2, u3} S M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_3))) (SMulWithZero.toSmulZeroClass.{u2, u3} S M (MulZeroClass.toHasZero.{u2} S (MulZeroOneClass.toMulZeroClass.{u2} S (MonoidWithZero.toMulZeroOneClass.{u2} S (Semiring.toMonoidWithZero.{u2} S _inst_2)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_3))) (MulActionWithZero.toSMulWithZero.{u2, u3} S M (Semiring.toMonoidWithZero.{u2} S _inst_2) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_3))) (Module.toMulActionWithZero.{u2, u3} S M _inst_2 _inst_3 _inst_5)))) (SMulZeroClass.toHasSmul.{u1, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_3))) (SMulWithZero.toSmulZeroClass.{u1, u3} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_3))) (MulActionWithZero.toSMulWithZero.{u1, u3} R M (Semiring.toMonoidWithZero.{u1} R _inst_1) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_3))) (Module.toMulActionWithZero.{u1, u3} R M _inst_1 _inst_3 _inst_6))))], (IsNoetherian.{u1, u3} R M _inst_1 _inst_3 _inst_6) -> (IsNoetherian.{u2, u3} S M _inst_2 _inst_3 _inst_5)
but is expected to have type
  forall (R : Type.{u3}) {S : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u3} R] [_inst_2 : Semiring.{u2} S] [_inst_3 : AddCommMonoid.{u1} M] [_inst_4 : SMul.{u3, u2} R S] [_inst_5 : Module.{u2, u1} S M _inst_2 _inst_3] [_inst_6 : Module.{u3, u1} R M _inst_1 _inst_3] [_inst_7 : IsScalarTower.{u3, u2, u1} R S M _inst_4 (SMulZeroClass.toSMul.{u2, u1} S M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_3)) (SMulWithZero.toSMulZeroClass.{u2, u1} S M (MonoidWithZero.toZero.{u2} S (Semiring.toMonoidWithZero.{u2} S _inst_2)) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_3)) (MulActionWithZero.toSMulWithZero.{u2, u1} S M (Semiring.toMonoidWithZero.{u2} S _inst_2) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_3)) (Module.toMulActionWithZero.{u2, u1} S M _inst_2 _inst_3 _inst_5)))) (SMulZeroClass.toSMul.{u3, u1} R M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_3)) (SMulWithZero.toSMulZeroClass.{u3, u1} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_3)) (MulActionWithZero.toSMulWithZero.{u3, u1} R M (Semiring.toMonoidWithZero.{u3} R _inst_1) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_3)) (Module.toMulActionWithZero.{u3, u1} R M _inst_1 _inst_3 _inst_6))))], (IsNoetherian.{u3, u1} R M _inst_1 _inst_3 _inst_6) -> (IsNoetherian.{u2, u1} S M _inst_2 _inst_3 _inst_5)
Case conversion may be inaccurate. Consider using '#align is_noetherian_of_tower isNoetherian_of_towerₓ'. -/
/-- If `M / S / R` is a scalar tower, and `M / R` is Noetherian, then `M / S` is
also noetherian. -/
theorem isNoetherian_of_tower (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M] [SMul R S]
    [Module S M] [Module R M] [IsScalarTower R S M] (h : IsNoetherian R M) : IsNoetherian S M :=
  by
  rw [isNoetherian_iff_wellFounded] at h⊢
  refine' (Submodule.restrictScalarsEmbedding R S M).dual.WellFounded h
#align is_noetherian_of_tower isNoetherian_of_tower

/- warning: is_noetherian_of_fg_of_noetherian -> isNoetherian_of_fg_of_noetherian is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (N : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) [_inst_4 : IsNoetherianRing.{u1} R (Ring.toSemiring.{u1} R _inst_1)], (Submodule.Fg.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 N) -> (IsNoetherian.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) N) (Ring.toSemiring.{u1} R _inst_1) (Submodule.addCommMonoid.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 N) (Submodule.module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 N))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] (N : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) [_inst_4 : IsNoetherianRing.{u2} R (Ring.toSemiring.{u2} R _inst_1)], (Submodule.Fg.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 N) -> (IsNoetherian.{u2, u1} R (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) M (Submodule.setLike.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3)) x N)) (Ring.toSemiring.{u2} R _inst_1) (Submodule.addCommMonoid.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 N) (Submodule.module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 N))
Case conversion may be inaccurate. Consider using '#align is_noetherian_of_fg_of_noetherian isNoetherian_of_fg_of_noetherianₓ'. -/
theorem isNoetherian_of_fg_of_noetherian {R M} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [IsNoetherianRing R] (hN : N.Fg) : IsNoetherian R N :=
  by
  let ⟨s, hs⟩ := hN
  haveI := Classical.decEq M
  haveI := Classical.decEq R
  letI : IsNoetherian R R := by infer_instance
  have : ∀ x ∈ s, x ∈ N := fun x hx => hs ▸ Submodule.subset_span hx
  refine'
    @isNoetherian_of_surjective ((↑s : Set M) → R) _ _ _ (Pi.module _ _ _) _ _ _ isNoetherian_pi
  · fapply LinearMap.mk
    · exact fun f => ⟨∑ i in s.attach, f i • i.1, N.sum_mem fun c _ => N.smul_mem _ <| this _ c.2⟩
    · intro f g
      apply Subtype.eq
      change (∑ i in s.attach, (f i + g i) • _) = _
      simp only [add_smul, Finset.sum_add_distrib]
      rfl
    · intro c f
      apply Subtype.eq
      change (∑ i in s.attach, (c • f i) • _) = _
      simp only [smul_eq_mul, mul_smul]
      exact finset.smul_sum.symm
  rw [LinearMap.range_eq_top]
  rintro ⟨n, hn⟩
  change n ∈ N at hn
  rw [← hs, ← Set.image_id ↑s, Finsupp.mem_span_image_iff_total] at hn
  rcases hn with ⟨l, hl1, hl2⟩
  refine' ⟨fun x => l x, Subtype.ext _⟩
  change (∑ i in s.attach, l i • (i : M)) = n
  rw [@Finset.sum_attach M M s _ fun i => l i • i, ← hl2, Finsupp.total_apply, Finsupp.sum, eq_comm]
  refine' Finset.sum_subset hl1 fun x _ hx => _
  rw [Finsupp.not_mem_support_iff.1 hx, zero_smul]
#align is_noetherian_of_fg_of_noetherian isNoetherian_of_fg_of_noetherian

/- warning: is_noetherian_of_fg_of_noetherian' -> isNoetherian_of_fg_of_noetherian' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_4 : IsNoetherianRing.{u1} R (Ring.toSemiring.{u1} R _inst_1)], (Submodule.Fg.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 (Top.top.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasTop.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))) -> (IsNoetherian.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] [_inst_4 : IsNoetherianRing.{u2} R (Ring.toSemiring.{u2} R _inst_1)], (Submodule.Fg.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 (Top.top.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.instTopSubmodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3))) -> (IsNoetherian.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3)
Case conversion may be inaccurate. Consider using '#align is_noetherian_of_fg_of_noetherian' isNoetherian_of_fg_of_noetherian'ₓ'. -/
theorem isNoetherian_of_fg_of_noetherian' {R M} [Ring R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] (h : (⊤ : Submodule R M).Fg) : IsNoetherian R M :=
  have : IsNoetherian R (⊤ : Submodule R M) := isNoetherian_of_fg_of_noetherian _ h
  isNoetherian_of_linearEquiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl)
#align is_noetherian_of_fg_of_noetherian' isNoetherian_of_fg_of_noetherian'

/- warning: is_noetherian_span_of_finite -> isNoetherian_span_of_finite is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_4 : IsNoetherianRing.{u1} R (Ring.toSemiring.{u1} R _inst_1)] {A : Set.{u2} M}, (Set.Finite.{u2} M A) -> (IsNoetherian.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) (Submodule.span.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 A)) (Ring.toSemiring.{u1} R _inst_1) (Submodule.addCommMonoid.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 (Submodule.span.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 A)) (Submodule.module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 (Submodule.span.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 A)))
but is expected to have type
  forall (R : Type.{u2}) {M : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] [_inst_4 : IsNoetherianRing.{u2} R (Ring.toSemiring.{u2} R _inst_1)] {A : Set.{u1} M}, (Set.Finite.{u1} M A) -> (IsNoetherian.{u2, u1} R (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) M (Submodule.setLike.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3)) x (Submodule.span.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 A))) (Ring.toSemiring.{u2} R _inst_1) (Submodule.addCommMonoid.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 (Submodule.span.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 A)) (Submodule.module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 (Submodule.span.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 A)))
Case conversion may be inaccurate. Consider using '#align is_noetherian_span_of_finite isNoetherian_span_of_finiteₓ'. -/
/-- In a module over a noetherian ring, the submodule generated by finitely many vectors is
noetherian. -/
theorem isNoetherian_span_of_finite (R) {M} [Ring R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] {A : Set M} (hA : A.Finite) : IsNoetherian R (Submodule.span R A) :=
  isNoetherian_of_fg_of_noetherian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)
#align is_noetherian_span_of_finite isNoetherian_span_of_finite

/- warning: is_noetherian_ring_of_surjective -> isNoetherianRing_of_surjective is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] (S : Type.{u2}) [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), (Function.Surjective.{succ u1, succ u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f)) -> (forall [H : IsNoetherianRing.{u1} R (Ring.toSemiring.{u1} R _inst_1)], IsNoetherianRing.{u2} S (Ring.toSemiring.{u2} S _inst_2))
but is expected to have type
  forall (R : Type.{u2}) [_inst_1 : Ring.{u2} R] (S : Type.{u1}) [_inst_2 : Ring.{u1} S] (f : RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2))), (Function.Surjective.{succ u2, succ u1} R S (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2))) R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2)) (RingHom.instRingHomClassRingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2)))))) f)) -> (forall [H : IsNoetherianRing.{u2} R (Ring.toSemiring.{u2} R _inst_1)], IsNoetherianRing.{u1} S (Ring.toSemiring.{u1} S _inst_2))
Case conversion may be inaccurate. Consider using '#align is_noetherian_ring_of_surjective isNoetherianRing_of_surjectiveₓ'. -/
theorem isNoetherianRing_of_surjective (R) [Ring R] (S) [Ring S] (f : R →+* S)
    (hf : Function.Surjective f) [H : IsNoetherianRing R] : IsNoetherianRing S :=
  by
  rw [isNoetherianRing_iff, isNoetherian_iff_wellFounded] at H⊢
  exact OrderEmbedding.wellFounded (Ideal.orderEmbeddingOfSurjective f hf).dual H
#align is_noetherian_ring_of_surjective isNoetherianRing_of_surjective

/- warning: is_noetherian_ring_range -> isNoetherianRing_range is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {S : Type.{u2}} [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) [_inst_3 : IsNoetherianRing.{u1} R (Ring.toSemiring.{u1} R _inst_1)], IsNoetherianRing.{u2} (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (Ring.toSemiring.{u2} (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (Subring.toRing.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {S : Type.{u2}} [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) [_inst_3 : IsNoetherianRing.{u1} R (Ring.toSemiring.{u1} R _inst_1)], IsNoetherianRing.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (Ring.toSemiring.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (Subring.toRing.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)))
Case conversion may be inaccurate. Consider using '#align is_noetherian_ring_range isNoetherianRing_rangeₓ'. -/
instance isNoetherianRing_range {R} [Ring R] {S} [Ring S] (f : R →+* S) [IsNoetherianRing R] :
    IsNoetherianRing f.range :=
  isNoetherianRing_of_surjective R f.range f.range_restrict f.rangeRestrict_surjective
#align is_noetherian_ring_range isNoetherianRing_range

/- warning: is_noetherian_ring_of_ring_equiv -> isNoetherianRing_of_ringEquiv is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] {S : Type.{u2}} [_inst_2 : Ring.{u2} S], (RingEquiv.{u1, u2} R S (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1)) (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R _inst_1)) (Distrib.toHasMul.{u2} S (Ring.toDistrib.{u2} S _inst_2)) (Distrib.toHasAdd.{u2} S (Ring.toDistrib.{u2} S _inst_2))) -> (forall [_inst_3 : IsNoetherianRing.{u1} R (Ring.toSemiring.{u1} R _inst_1)], IsNoetherianRing.{u2} S (Ring.toSemiring.{u2} S _inst_2))
but is expected to have type
  forall (R : Type.{u2}) [_inst_1 : Ring.{u2} R] {S : Type.{u1}} [_inst_2 : Ring.{u1} S], (RingEquiv.{u2, u1} R S (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1))) (NonUnitalNonAssocRing.toMul.{u1} S (NonAssocRing.toNonUnitalNonAssocRing.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2))) (Distrib.toAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1))))) (Distrib.toAdd.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} S (NonAssocRing.toNonUnitalNonAssocRing.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2)))))) -> (forall [_inst_3 : IsNoetherianRing.{u2} R (Ring.toSemiring.{u2} R _inst_1)], IsNoetherianRing.{u1} S (Ring.toSemiring.{u1} S _inst_2))
Case conversion may be inaccurate. Consider using '#align is_noetherian_ring_of_ring_equiv isNoetherianRing_of_ringEquivₓ'. -/
theorem isNoetherianRing_of_ringEquiv (R) [Ring R] {S} [Ring S] (f : R ≃+* S) [IsNoetherianRing R] :
    IsNoetherianRing S :=
  isNoetherianRing_of_surjective R S f.toRingHom f.toEquiv.Surjective
#align is_noetherian_ring_of_ring_equiv isNoetherianRing_of_ringEquiv

/- warning: is_noetherian_ring.is_nilpotent_nilradical -> IsNoetherianRing.isNilpotent_nilradical is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] [_inst_2 : IsNoetherianRing.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))], IsNilpotent.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (MulZeroClass.toHasZero.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (IdemSemiring.toSemiring.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Submodule.idemSemiring.{u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))))) (Monoid.Pow.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (MonoidWithZero.toMonoid.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toMonoidWithZero.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (IdemSemiring.toSemiring.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Submodule.idemSemiring.{u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))))) (nilradical.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] [_inst_2 : IsNoetherianRing.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))], IsNilpotent.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (CommMonoidWithZero.toZero.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (CommSemiring.toCommMonoidWithZero.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (IdemCommSemiring.toCommSemiring.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instIdemCommSemiringIdealToSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (Monoid.Pow.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (MonoidWithZero.toMonoid.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toMonoidWithZero.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (IdemSemiring.toSemiring.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Submodule.idemSemiring.{u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))))) (nilradical.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align is_noetherian_ring.is_nilpotent_nilradical IsNoetherianRing.isNilpotent_nilradicalₓ'. -/
theorem IsNoetherianRing.isNilpotent_nilradical (R : Type _) [CommRing R] [IsNoetherianRing R] :
    IsNilpotent (nilradical R) :=
  by
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg (⊥ : Ideal R) (IsNoetherian.noetherian _)
  exact ⟨n, eq_bot_iff.mpr hn⟩
#align is_noetherian_ring.is_nilpotent_nilradical IsNoetherianRing.isNilpotent_nilradical

