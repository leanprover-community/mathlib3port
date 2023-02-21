/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.analysis.topology
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Analysis.Filter
import Mathbin.Topology.Bases

/-!
# Computational realization of topological spaces (experimental)

This file provides infrastructure to compute with topological spaces.

## Main declarations

* `ctop`: Realization of a topology basis.
* `ctop.realizer`: Realization of a topological space. `ctop` that generates the given topology.
* `locally_finite.realizer`: Realization of the local finiteness of an indexed family of sets.
* `compact.realizer`: Realization of the compactness of a set.
-/


open Set

open Filter hiding Realizer

open Topology

#print Ctop /-
/-- A `ctop α σ` is a realization of a topology (basis) on `α`,
  represented by a type `σ` together with operations for the top element and
  the intersection operation. -/
structure Ctop (α σ : Type _) where
  f : σ → Set α
  top : α → σ
  top_mem : ∀ x : α, x ∈ f (top x)
  inter : ∀ (a b) (x : α), x ∈ f a ∩ f b → σ
  inter_mem : ∀ a b x h, x ∈ f (inter a b x h)
  inter_sub : ∀ a b x h, f (inter a b x h) ⊆ f a ∩ f b
#align ctop Ctop
-/

variable {α : Type _} {β : Type _} {σ : Type _} {τ : Type _}

instance : Inhabited (Ctop α (Set α)) :=
  ⟨{  f := id
      top := singleton
      top_mem := mem_singleton
      inter := fun s t _ _ => s ∩ t
      inter_mem := fun s t a => id
      inter_sub := fun s t a ha => Subset.rfl }⟩

namespace Ctop

section

variable (F : Ctop α σ)

instance : CoeFun (Ctop α σ) fun _ => σ → Set α :=
  ⟨Ctop.f⟩

/- warning: ctop.coe_mk -> Ctop.coe_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} (f : σ -> (Set.{u1} α)) (T : α -> σ) (h₁ : forall (x : α), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (f (T x))) (I : forall (a : σ) (b : σ) (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (f a) (f b))) -> σ) (h₂ : forall (a : σ) (b : σ) (x : α) (h : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (f a) (f b))), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (f (I a b x h))) (h₃ : forall (a : σ) (b : σ) (x : α) (h : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (f a) (f b))), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (f (I a b x h)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (f a) (f b))) (a : σ), Eq.{succ u1} (Set.{u1} α) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α σ) (fun (_x : Ctop.{u1, u2} α σ) => σ -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α σ) (Ctop.mk.{u1, u2} α σ f T h₁ I h₂ h₃) a) (f a)
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} (f : σ -> (Set.{u2} α)) (T : α -> σ) (h₁ : forall (x : α), Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (f (T x))) (I : forall (a : σ) (b : σ) (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (f a) (f b))) -> σ) (h₂ : forall (a : σ) (b : σ) (x : α) (h : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (f a) (f b))), Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (f (I a b x h))) (h₃ : forall (a : σ) (b : σ) (x : α) (h : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (f a) (f b))), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (f (I a b x h)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (f a) (f b))) (a : σ), Eq.{succ u2} (Set.{u2} α) (Ctop.f.{u2, u1} α σ (Ctop.mk.{u2, u1} α σ f T h₁ I h₂ h₃) a) (f a)
Case conversion may be inaccurate. Consider using '#align ctop.coe_mk Ctop.coe_mkₓ'. -/
@[simp]
theorem coe_mk (f T h₁ I h₂ h₃ a) : (@Ctop.mk α σ f T h₁ I h₂ h₃) a = f a :=
  rfl
#align ctop.coe_mk Ctop.coe_mk

#print Ctop.ofEquiv /-
/-- Map a ctop to an equivalent representation type. -/
def ofEquiv (E : σ ≃ τ) : Ctop α σ → Ctop α τ
  | ⟨f, T, h₁, I, h₂, h₃⟩ =>
    { f := fun a => f (E.symm a)
      top := fun x => E (T x)
      top_mem := fun x => by simpa using h₁ x
      inter := fun a b x h => E (I (E.symm a) (E.symm b) x h)
      inter_mem := fun a b x h => by simpa using h₂ (E.symm a) (E.symm b) x h
      inter_sub := fun a b x h => by simpa using h₃ (E.symm a) (E.symm b) x h }
#align ctop.of_equiv Ctop.ofEquiv
-/

/- warning: ctop.of_equiv_val -> Ctop.ofEquiv_val is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} {τ : Type.{u3}} (E : Equiv.{succ u2, succ u3} σ τ) (F : Ctop.{u1, u2} α σ) (a : τ), Eq.{succ u1} (Set.{u1} α) (coeFn.{max (succ u1) (succ u3), max (succ u3) (succ u1)} (Ctop.{u1, u3} α τ) (fun (_x : Ctop.{u1, u3} α τ) => τ -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u3} α τ) (Ctop.ofEquiv.{u1, u2, u3} α σ τ E F) a) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α σ) (fun (_x : Ctop.{u1, u2} α σ) => σ -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α σ) F (coeFn.{max 1 (max (succ u3) (succ u2)) (succ u2) (succ u3), max (succ u3) (succ u2)} (Equiv.{succ u3, succ u2} τ σ) (fun (_x : Equiv.{succ u3, succ u2} τ σ) => τ -> σ) (Equiv.hasCoeToFun.{succ u3, succ u2} τ σ) (Equiv.symm.{succ u2, succ u3} σ τ E) a))
but is expected to have type
  forall {α : Type.{u1}} {σ : Type.{u3}} {τ : Type.{u2}} (E : Equiv.{succ u3, succ u2} σ τ) (F : Ctop.{u1, u3} α σ) (a : τ), Eq.{succ u1} (Set.{u1} α) (Ctop.f.{u1, u2} α τ (Ctop.ofEquiv.{u1, u3, u2} α σ τ E F) a) (Ctop.f.{u1, u3} α σ F (FunLike.coe.{max (succ u3) (succ u2), succ u2, succ u3} (Equiv.{succ u2, succ u3} τ σ) τ (fun (_x : τ) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : τ) => σ) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u3} τ σ) (Equiv.symm.{succ u3, succ u2} σ τ E) a))
Case conversion may be inaccurate. Consider using '#align ctop.of_equiv_val Ctop.ofEquiv_valₓ'. -/
@[simp]
theorem ofEquiv_val (E : σ ≃ τ) (F : Ctop α σ) (a : τ) : F.of_equiv E a = F (E.symm a) := by
  cases F <;> rfl
#align ctop.of_equiv_val Ctop.ofEquiv_val

end

#print Ctop.toTopsp /-
/-- Every `ctop` is a topological space. -/
def toTopsp (F : Ctop α σ) : TopologicalSpace α :=
  TopologicalSpace.generateFrom (Set.range F.f)
#align ctop.to_topsp Ctop.toTopsp
-/

/- warning: ctop.to_topsp_is_topological_basis -> Ctop.toTopsp_isTopologicalBasis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} (F : Ctop.{u1, u2} α σ), TopologicalSpace.IsTopologicalBasis.{u1} α (Ctop.toTopsp.{u1, u2} α σ F) (Set.range.{u1, succ u2} (Set.{u1} α) σ (Ctop.f.{u1, u2} α σ F))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} (F : Ctop.{u2, u1} α σ), TopologicalSpace.IsTopologicalBasis.{u2} α (Ctop.toTopsp.{u2, u1} α σ F) (Set.range.{u2, succ u1} (Set.{u2} α) σ (Ctop.f.{u2, u1} α σ F))
Case conversion may be inaccurate. Consider using '#align ctop.to_topsp_is_topological_basis Ctop.toTopsp_isTopologicalBasisₓ'. -/
theorem toTopsp_isTopologicalBasis (F : Ctop α σ) :
    @TopologicalSpace.IsTopologicalBasis _ F.toTopsp (Set.range F.f) :=
  letI := F.to_topsp
  ⟨fun u ⟨a, e₁⟩ v ⟨b, e₂⟩ =>
    e₁ ▸ e₂ ▸ fun x h => ⟨_, ⟨_, rfl⟩, F.inter_mem a b x h, F.inter_sub a b x h⟩,
    eq_univ_iff_forall.2 fun x => ⟨_, ⟨_, rfl⟩, F.top_mem x⟩, rfl⟩
#align ctop.to_topsp_is_topological_basis Ctop.toTopsp_isTopologicalBasis

/- warning: ctop.mem_nhds_to_topsp -> Ctop.mem_nhds_toTopsp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : Type.{u2}} (F : Ctop.{u1, u2} α σ) {s : Set.{u1} α} {a : α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α (Ctop.toTopsp.{u1, u2} α σ F) a)) (Exists.{succ u2} σ (fun (b : σ) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α σ) (fun (_x : Ctop.{u1, u2} α σ) => σ -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α σ) F b)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α σ) (fun (_x : Ctop.{u1, u2} α σ) => σ -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α σ) F b) s)))
but is expected to have type
  forall {α : Type.{u2}} {σ : Type.{u1}} (F : Ctop.{u2, u1} α σ) {s : Set.{u2} α} {a : α}, Iff (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (nhds.{u2} α (Ctop.toTopsp.{u2, u1} α σ F) a)) (Exists.{succ u1} σ (fun (b : σ) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Ctop.f.{u2, u1} α σ F b)) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Ctop.f.{u2, u1} α σ F b) s)))
Case conversion may be inaccurate. Consider using '#align ctop.mem_nhds_to_topsp Ctop.mem_nhds_toTopspₓ'. -/
@[simp]
theorem mem_nhds_toTopsp (F : Ctop α σ) {s : Set α} {a : α} :
    s ∈ @nhds _ F.toTopsp a ↔ ∃ b, a ∈ F b ∧ F b ⊆ s :=
  (@TopologicalSpace.IsTopologicalBasis.mem_nhds_iff _ F.toTopsp _ _ _
        F.toTopsp_isTopologicalBasis).trans <|
    ⟨fun ⟨_, ⟨x, rfl⟩, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨_, ⟨x, rfl⟩, h⟩⟩
#align ctop.mem_nhds_to_topsp Ctop.mem_nhds_toTopsp

end Ctop

#print Ctop.Realizer /-
/-- A `ctop` realizer for the topological space `T` is a `ctop`
  which generates `T`. -/
structure Ctop.Realizer (α) [T : TopologicalSpace α] where
  σ : Type _
  f : Ctop α σ
  Eq : F.toTopsp = T
#align ctop.realizer Ctop.Realizer
-/

open Ctop

#print Ctop.toRealizer /-
/-- A `ctop` realizes the topological space it generates. -/
protected def Ctop.toRealizer (F : Ctop α σ) : @Ctop.Realizer _ F.toTopsp :=
  @Ctop.Realizer.mk _ F.toTopsp σ F rfl
#align ctop.to_realizer Ctop.toRealizer
-/

instance (F : Ctop α σ) : Inhabited (@Ctop.Realizer _ F.toTopsp) :=
  ⟨F.toRealizer⟩

namespace Ctop.Realizer

/- warning: ctop.realizer.is_basis -> Ctop.Realizer.is_basis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [T : TopologicalSpace.{u1} α] (F : Ctop.Realizer.{u1, u2} α T), TopologicalSpace.IsTopologicalBasis.{u1} α T (Set.range.{u1, succ u2} (Set.{u1} α) (Ctop.Realizer.σ.{u1, u2} α T F) (Ctop.f.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α T F) (Ctop.Realizer.f.{u1, u2} α T F)))
but is expected to have type
  forall {α : Type.{u2}} [T : TopologicalSpace.{u2} α] (F : Ctop.Realizer.{u2, u1} α T), TopologicalSpace.IsTopologicalBasis.{u2} α T (Set.range.{u2, succ u1} (Set.{u2} α) (Ctop.Realizer.σ.{u2, u1} α T F) (Ctop.f.{u2, u1} α (Ctop.Realizer.σ.{u2, u1} α T F) (Ctop.Realizer.F.{u2, u1} α T F)))
Case conversion may be inaccurate. Consider using '#align ctop.realizer.is_basis Ctop.Realizer.is_basisₓ'. -/
protected theorem is_basis [T : TopologicalSpace α] (F : Realizer α) :
    TopologicalSpace.IsTopologicalBasis (Set.range F.f.f) := by
  have := to_topsp_is_topological_basis F.F <;> rwa [F.eq] at this
#align ctop.realizer.is_basis Ctop.Realizer.is_basis

/- warning: ctop.realizer.mem_nhds -> Ctop.Realizer.mem_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [T : TopologicalSpace.{u1} α] (F : Ctop.Realizer.{u1, u2} α T) {s : Set.{u1} α} {a : α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α T a)) (Exists.{succ u2} (Ctop.Realizer.σ.{u1, u2} α T F) (fun (b : Ctop.Realizer.σ.{u1, u2} α T F) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α T F)) (fun (_x : Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α T F)) => (Ctop.Realizer.σ.{u1, u2} α T F) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α T F)) (Ctop.Realizer.f.{u1, u2} α T F) b)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α T F)) (fun (_x : Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α T F)) => (Ctop.Realizer.σ.{u1, u2} α T F) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α T F)) (Ctop.Realizer.f.{u1, u2} α T F) b) s)))
but is expected to have type
  forall {α : Type.{u2}} [T : TopologicalSpace.{u2} α] (F : Ctop.Realizer.{u2, u1} α T) {s : Set.{u2} α} {a : α}, Iff (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (nhds.{u2} α T a)) (Exists.{succ u1} (Ctop.Realizer.σ.{u2, u1} α T F) (fun (b : Ctop.Realizer.σ.{u2, u1} α T F) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Ctop.f.{u2, u1} α (Ctop.Realizer.σ.{u2, u1} α T F) (Ctop.Realizer.F.{u2, u1} α T F) b)) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Ctop.f.{u2, u1} α (Ctop.Realizer.σ.{u2, u1} α T F) (Ctop.Realizer.F.{u2, u1} α T F) b) s)))
Case conversion may be inaccurate. Consider using '#align ctop.realizer.mem_nhds Ctop.Realizer.mem_nhdsₓ'. -/
protected theorem mem_nhds [T : TopologicalSpace α] (F : Realizer α) {s : Set α} {a : α} :
    s ∈ 𝓝 a ↔ ∃ b, a ∈ F.f b ∧ F.f b ⊆ s := by have := mem_nhds_to_topsp F.F <;> rwa [F.eq] at this
#align ctop.realizer.mem_nhds Ctop.Realizer.mem_nhds

/- warning: ctop.realizer.is_open_iff -> Ctop.Realizer.isOpen_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (F : Ctop.Realizer.{u1, u2} α _inst_1) {s : Set.{u1} α}, Iff (IsOpen.{u1} α _inst_1 s) (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Exists.{succ u2} (Ctop.Realizer.σ.{u1, u2} α _inst_1 F) (fun (b : Ctop.Realizer.σ.{u1, u2} α _inst_1 F) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (fun (_x : Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) => (Ctop.Realizer.σ.{u1, u2} α _inst_1 F) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (Ctop.Realizer.f.{u1, u2} α _inst_1 F) b)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (fun (_x : Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) => (Ctop.Realizer.σ.{u1, u2} α _inst_1 F) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (Ctop.Realizer.f.{u1, u2} α _inst_1 F) b) s))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] (F : Ctop.Realizer.{u2, u1} α _inst_1) {s : Set.{u2} α}, Iff (IsOpen.{u2} α _inst_1 s) (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (Exists.{succ u1} (Ctop.Realizer.σ.{u2, u1} α _inst_1 F) (fun (b : Ctop.Realizer.σ.{u2, u1} α _inst_1 F) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Ctop.f.{u2, u1} α (Ctop.Realizer.σ.{u2, u1} α _inst_1 F) (Ctop.Realizer.F.{u2, u1} α _inst_1 F) b)) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Ctop.f.{u2, u1} α (Ctop.Realizer.σ.{u2, u1} α _inst_1 F) (Ctop.Realizer.F.{u2, u1} α _inst_1 F) b) s))))
Case conversion may be inaccurate. Consider using '#align ctop.realizer.is_open_iff Ctop.Realizer.isOpen_iffₓ'. -/
theorem isOpen_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} :
    IsOpen s ↔ ∀ a ∈ s, ∃ b, a ∈ F.f b ∧ F.f b ⊆ s :=
  isOpen_iff_mem_nhds.trans <| ball_congr fun a h => F.mem_nhds
#align ctop.realizer.is_open_iff Ctop.Realizer.isOpen_iff

/- warning: ctop.realizer.is_closed_iff -> Ctop.Realizer.isClosed_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (F : Ctop.Realizer.{u1, u2} α _inst_1) {s : Set.{u1} α}, Iff (IsClosed.{u1} α _inst_1 s) (forall (a : α), (forall (b : Ctop.Realizer.σ.{u1, u2} α _inst_1 F), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (fun (_x : Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) => (Ctop.Realizer.σ.{u1, u2} α _inst_1 F) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (Ctop.Realizer.f.{u1, u2} α _inst_1 F) b)) -> (Exists.{succ u1} α (fun (z : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (fun (_x : Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) => (Ctop.Realizer.σ.{u1, u2} α _inst_1 F) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (Ctop.Realizer.f.{u1, u2} α _inst_1 F) b) s)))) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] (F : Ctop.Realizer.{u2, u1} α _inst_1) {s : Set.{u2} α}, Iff (IsClosed.{u2} α _inst_1 s) (forall (a : α), (forall (b : Ctop.Realizer.σ.{u2, u1} α _inst_1 F), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Ctop.f.{u2, u1} α (Ctop.Realizer.σ.{u2, u1} α _inst_1 F) (Ctop.Realizer.F.{u2, u1} α _inst_1 F) b)) -> (Exists.{succ u2} α (fun (z : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) z (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (Ctop.f.{u2, u1} α (Ctop.Realizer.σ.{u2, u1} α _inst_1 F) (Ctop.Realizer.F.{u2, u1} α _inst_1 F) b) s)))) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s))
Case conversion may be inaccurate. Consider using '#align ctop.realizer.is_closed_iff Ctop.Realizer.isClosed_iffₓ'. -/
theorem isClosed_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} :
    IsClosed s ↔ ∀ a, (∀ b, a ∈ F.f b → ∃ z, z ∈ F.f b ∩ s) → a ∈ s :=
  isOpen_compl_iff.symm.trans <|
    F.isOpen_iff.trans <|
      forall_congr' fun a =>
        show (a ∉ s → ∃ b : F.σ, a ∈ F.f b ∧ ∀ z ∈ F.f b, z ∉ s) ↔ _ by
          haveI := Classical.propDecidable <;> rw [not_imp_comm] <;>
            simp [not_exists, not_and, not_forall, and_comm']
#align ctop.realizer.is_closed_iff Ctop.Realizer.isClosed_iff

/- warning: ctop.realizer.mem_interior_iff -> Ctop.Realizer.mem_interior_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (F : Ctop.Realizer.{u1, u2} α _inst_1) {s : Set.{u1} α} {a : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (interior.{u1} α _inst_1 s)) (Exists.{succ u2} (Ctop.Realizer.σ.{u1, u2} α _inst_1 F) (fun (b : Ctop.Realizer.σ.{u1, u2} α _inst_1 F) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (fun (_x : Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) => (Ctop.Realizer.σ.{u1, u2} α _inst_1 F) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (Ctop.Realizer.f.{u1, u2} α _inst_1 F) b)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (fun (_x : Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) => (Ctop.Realizer.σ.{u1, u2} α _inst_1 F) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (Ctop.Realizer.f.{u1, u2} α _inst_1 F) b) s)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] (F : Ctop.Realizer.{u2, u1} α _inst_1) {s : Set.{u2} α} {a : α}, Iff (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (interior.{u2} α _inst_1 s)) (Exists.{succ u1} (Ctop.Realizer.σ.{u2, u1} α _inst_1 F) (fun (b : Ctop.Realizer.σ.{u2, u1} α _inst_1 F) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Ctop.f.{u2, u1} α (Ctop.Realizer.σ.{u2, u1} α _inst_1 F) (Ctop.Realizer.F.{u2, u1} α _inst_1 F) b)) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Ctop.f.{u2, u1} α (Ctop.Realizer.σ.{u2, u1} α _inst_1 F) (Ctop.Realizer.F.{u2, u1} α _inst_1 F) b) s)))
Case conversion may be inaccurate. Consider using '#align ctop.realizer.mem_interior_iff Ctop.Realizer.mem_interior_iffₓ'. -/
theorem mem_interior_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} {a : α} :
    a ∈ interior s ↔ ∃ b, a ∈ F.f b ∧ F.f b ⊆ s :=
  mem_interior_iff_mem_nhds.trans F.mem_nhds
#align ctop.realizer.mem_interior_iff Ctop.Realizer.mem_interior_iff

/- warning: ctop.realizer.is_open -> Ctop.Realizer.isOpen is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (F : Ctop.Realizer.{u1, u2} α _inst_1) (s : Ctop.Realizer.σ.{u1, u2} α _inst_1 F), IsOpen.{u1} α _inst_1 (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (fun (_x : Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) => (Ctop.Realizer.σ.{u1, u2} α _inst_1 F) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (Ctop.Realizer.f.{u1, u2} α _inst_1 F) s)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] (F : Ctop.Realizer.{u2, u1} α _inst_1) (s : Ctop.Realizer.σ.{u2, u1} α _inst_1 F), IsOpen.{u2} α _inst_1 (Ctop.f.{u2, u1} α (Ctop.Realizer.σ.{u2, u1} α _inst_1 F) (Ctop.Realizer.F.{u2, u1} α _inst_1 F) s)
Case conversion may be inaccurate. Consider using '#align ctop.realizer.is_open Ctop.Realizer.isOpenₓ'. -/
protected theorem isOpen [TopologicalSpace α] (F : Realizer α) (s : F.σ) : IsOpen (F.f s) :=
  isOpen_iff_nhds.2 fun a m => by simpa using F.mem_nhds.2 ⟨s, m, subset.refl _⟩
#align ctop.realizer.is_open Ctop.Realizer.isOpen

/- warning: ctop.realizer.ext' -> Ctop.Realizer.ext' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [T : TopologicalSpace.{u1} α] {σ : Type.{u2}} {F : Ctop.{u1, u2} α σ}, (forall (a : α) (s : Set.{u1} α), Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α T a)) (Exists.{succ u2} σ (fun (b : σ) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α σ) (fun (_x : Ctop.{u1, u2} α σ) => σ -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α σ) F b)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α σ) (fun (_x : Ctop.{u1, u2} α σ) => σ -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α σ) F b) s)))) -> (Eq.{succ u1} (TopologicalSpace.{u1} α) (Ctop.toTopsp.{u1, u2} α σ F) T)
but is expected to have type
  forall {α : Type.{u2}} [T : TopologicalSpace.{u2} α] {σ : Type.{u1}} {F : Ctop.{u2, u1} α σ}, (forall (a : α) (s : Set.{u2} α), Iff (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (nhds.{u2} α T a)) (Exists.{succ u1} σ (fun (b : σ) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Ctop.f.{u2, u1} α σ F b)) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Ctop.f.{u2, u1} α σ F b) s)))) -> (Eq.{succ u2} (TopologicalSpace.{u2} α) (Ctop.toTopsp.{u2, u1} α σ F) T)
Case conversion may be inaccurate. Consider using '#align ctop.realizer.ext' Ctop.Realizer.ext'ₓ'. -/
theorem ext' [T : TopologicalSpace α] {σ : Type _} {F : Ctop α σ}
    (H : ∀ a s, s ∈ 𝓝 a ↔ ∃ b, a ∈ F b ∧ F b ⊆ s) : F.toTopsp = T :=
  by
  refine' eq_of_nhds_eq_nhds fun x => _
  ext s
  rw [mem_nhds_to_topsp, H]
#align ctop.realizer.ext' Ctop.Realizer.ext'

/- warning: ctop.realizer.ext -> Ctop.Realizer.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [T : TopologicalSpace.{u1} α] {σ : Type.{u2}} {F : Ctop.{u1, u2} α σ}, (forall (a : σ), IsOpen.{u1} α T (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α σ) (fun (_x : Ctop.{u1, u2} α σ) => σ -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α σ) F a)) -> (forall (a : α) (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α T a)) -> (Exists.{succ u2} σ (fun (b : σ) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α σ) (fun (_x : Ctop.{u1, u2} α σ) => σ -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α σ) F b)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α σ) (fun (_x : Ctop.{u1, u2} α σ) => σ -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α σ) F b) s)))) -> (Eq.{succ u1} (TopologicalSpace.{u1} α) (Ctop.toTopsp.{u1, u2} α σ F) T)
but is expected to have type
  forall {α : Type.{u2}} [T : TopologicalSpace.{u2} α] {σ : Type.{u1}} {F : Ctop.{u2, u1} α σ}, (forall (a : σ), IsOpen.{u2} α T (Ctop.f.{u2, u1} α σ F a)) -> (forall (a : α) (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (nhds.{u2} α T a)) -> (Exists.{succ u1} σ (fun (b : σ) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Ctop.f.{u2, u1} α σ F b)) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Ctop.f.{u2, u1} α σ F b) s)))) -> (Eq.{succ u2} (TopologicalSpace.{u2} α) (Ctop.toTopsp.{u2, u1} α σ F) T)
Case conversion may be inaccurate. Consider using '#align ctop.realizer.ext Ctop.Realizer.extₓ'. -/
theorem ext [T : TopologicalSpace α] {σ : Type _} {F : Ctop α σ} (H₁ : ∀ a, IsOpen (F a))
    (H₂ : ∀ a s, s ∈ 𝓝 a → ∃ b, a ∈ F b ∧ F b ⊆ s) : F.toTopsp = T :=
  ext' fun a s => ⟨H₂ a s, fun ⟨b, h₁, h₂⟩ => mem_nhds_iff.2 ⟨_, h₂, H₁ _, h₁⟩⟩
#align ctop.realizer.ext Ctop.Realizer.ext

variable [TopologicalSpace α]

#print Ctop.Realizer.id /-
/-- The topological space realizer made of the open sets. -/
protected def id : Realizer α :=
  ⟨{ x : Set α // IsOpen x },
    { f := Subtype.val
      top := fun _ => ⟨univ, isOpen_univ⟩
      top_mem := mem_univ
      inter := fun ⟨x, h₁⟩ ⟨y, h₂⟩ a h₃ => ⟨_, h₁.inter h₂⟩
      inter_mem := fun ⟨x, h₁⟩ ⟨y, h₂⟩ a => id
      inter_sub := fun ⟨x, h₁⟩ ⟨y, h₂⟩ a h₃ => Subset.refl _ },
    ext Subtype.property fun x s h =>
      let ⟨t, h, o, m⟩ := mem_nhds_iff.1 h
      ⟨⟨t, o⟩, m, h⟩⟩
#align ctop.realizer.id Ctop.Realizer.id
-/

#print Ctop.Realizer.ofEquiv /-
/-- Replace the representation type of a `ctop` realizer. -/
def ofEquiv (F : Realizer α) (E : F.σ ≃ τ) : Realizer α :=
  ⟨τ, F.f.of_equiv E,
    ext' fun a s =>
      F.mem_nhds.trans <|
        ⟨fun ⟨s, h⟩ => ⟨E s, by simpa using h⟩, fun ⟨t, h⟩ => ⟨E.symm t, by simpa using h⟩⟩⟩
#align ctop.realizer.of_equiv Ctop.Realizer.ofEquiv
-/

/- warning: ctop.realizer.of_equiv_σ -> Ctop.Realizer.ofEquiv_σ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {τ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] (F : Ctop.Realizer.{u1, u3} α _inst_1) (E : Equiv.{succ u3, succ u2} (Ctop.Realizer.σ.{u1, u3} α _inst_1 F) τ), Eq.{succ (succ u2)} Type.{u2} (Ctop.Realizer.σ.{u1, u2} α _inst_1 (Ctop.Realizer.ofEquiv.{u1, u2, u3} α τ _inst_1 F E)) τ
but is expected to have type
  forall {α : Type.{u3}} {τ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] (F : Ctop.Realizer.{u3, u2} α _inst_1) (E : Equiv.{succ u2, succ u1} (Ctop.Realizer.σ.{u3, u2} α _inst_1 F) τ), Eq.{succ (succ u1)} Type.{u1} (Ctop.Realizer.σ.{u3, u1} α _inst_1 (Ctop.Realizer.ofEquiv.{u3, u1, u2} α τ _inst_1 F E)) τ
Case conversion may be inaccurate. Consider using '#align ctop.realizer.of_equiv_σ Ctop.Realizer.ofEquiv_σₓ'. -/
@[simp]
theorem ofEquiv_σ (F : Realizer α) (E : F.σ ≃ τ) : (F.of_equiv E).σ = τ :=
  rfl
#align ctop.realizer.of_equiv_σ Ctop.Realizer.ofEquiv_σ

/- warning: ctop.realizer.of_equiv_F -> Ctop.Realizer.ofEquiv_F is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {τ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] (F : Ctop.Realizer.{u1, u3} α _inst_1) (E : Equiv.{succ u3, succ u2} (Ctop.Realizer.σ.{u1, u3} α _inst_1 F) τ) (s : τ), Eq.{succ u1} (Set.{u1} α) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 (Ctop.Realizer.ofEquiv.{u1, u2, u3} α τ _inst_1 F E))) (fun (_x : Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 (Ctop.Realizer.ofEquiv.{u1, u2, u3} α τ _inst_1 F E))) => (Ctop.Realizer.σ.{u1, u2} α _inst_1 (Ctop.Realizer.ofEquiv.{u1, u2, u3} α τ _inst_1 F E)) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 (Ctop.Realizer.ofEquiv.{u1, u2, u3} α τ _inst_1 F E))) (Ctop.Realizer.f.{u1, u2} α _inst_1 (Ctop.Realizer.ofEquiv.{u1, u2, u3} α τ _inst_1 F E)) s) (coeFn.{max (succ u1) (succ u3), max (succ u3) (succ u1)} (Ctop.{u1, u3} α (Ctop.Realizer.σ.{u1, u3} α _inst_1 F)) (fun (_x : Ctop.{u1, u3} α (Ctop.Realizer.σ.{u1, u3} α _inst_1 F)) => (Ctop.Realizer.σ.{u1, u3} α _inst_1 F) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u3} α (Ctop.Realizer.σ.{u1, u3} α _inst_1 F)) (Ctop.Realizer.f.{u1, u3} α _inst_1 F) (coeFn.{max 1 (max (succ u2) (succ u3)) (succ u3) (succ u2), max (succ u2) (succ u3)} (Equiv.{succ u2, succ u3} τ (Ctop.Realizer.σ.{u1, u3} α _inst_1 F)) (fun (_x : Equiv.{succ u2, succ u3} τ (Ctop.Realizer.σ.{u1, u3} α _inst_1 F)) => τ -> (Ctop.Realizer.σ.{u1, u3} α _inst_1 F)) (Equiv.hasCoeToFun.{succ u2, succ u3} τ (Ctop.Realizer.σ.{u1, u3} α _inst_1 F)) (Equiv.symm.{succ u3, succ u2} (Ctop.Realizer.σ.{u1, u3} α _inst_1 F) τ E) s))
but is expected to have type
  forall {α : Type.{u3}} {τ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] (F : Ctop.Realizer.{u3, u2} α _inst_1) (E : Equiv.{succ u2, succ u1} (Ctop.Realizer.σ.{u3, u2} α _inst_1 F) τ) (s : τ), Eq.{succ u3} (Set.{u3} α) (Ctop.f.{u3, u1} α (Ctop.Realizer.σ.{u3, u1} α _inst_1 (Ctop.Realizer.ofEquiv.{u3, u1, u2} α τ _inst_1 F E)) (Ctop.Realizer.F.{u3, u1} α _inst_1 (Ctop.Realizer.ofEquiv.{u3, u1, u2} α τ _inst_1 F E)) s) (Ctop.f.{u3, u2} α (Ctop.Realizer.σ.{u3, u2} α _inst_1 F) (Ctop.Realizer.F.{u3, u2} α _inst_1 F) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Equiv.{succ u1, succ u2} τ (Ctop.Realizer.σ.{u3, u2} α _inst_1 F)) τ (fun (_x : τ) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : τ) => Ctop.Realizer.σ.{u3, u2} α _inst_1 F) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} τ (Ctop.Realizer.σ.{u3, u2} α _inst_1 F)) (Equiv.symm.{succ u2, succ u1} (Ctop.Realizer.σ.{u3, u2} α _inst_1 F) τ E) s))
Case conversion may be inaccurate. Consider using '#align ctop.realizer.of_equiv_F Ctop.Realizer.ofEquiv_Fₓ'. -/
@[simp]
theorem ofEquiv_F (F : Realizer α) (E : F.σ ≃ τ) (s : τ) : (F.of_equiv E).f s = F.f (E.symm s) := by
  delta of_equiv <;> simp
#align ctop.realizer.of_equiv_F Ctop.Realizer.ofEquiv_F

#print Ctop.Realizer.nhds /-
/-- A realizer of the neighborhood of a point. -/
protected def nhds (F : Realizer α) (a : α) : (𝓝 a).Realizer :=
  ⟨{ s : F.σ // a ∈ F.f s },
    { f := fun s => F.f s.1
      pt := ⟨_, F.f.top_mem a⟩
      inf := fun ⟨x, h₁⟩ ⟨y, h₂⟩ => ⟨_, F.f.inter_mem x y a ⟨h₁, h₂⟩⟩
      inf_le_left := fun ⟨x, h₁⟩ ⟨y, h₂⟩ z h => (F.f.inter_sub x y a ⟨h₁, h₂⟩ h).1
      inf_le_right := fun ⟨x, h₁⟩ ⟨y, h₂⟩ z h => (F.f.inter_sub x y a ⟨h₁, h₂⟩ h).2 },
    filter_eq <|
      Set.ext fun x =>
        ⟨fun ⟨⟨s, as⟩, h⟩ => mem_nhds_iff.2 ⟨_, h, F.IsOpen _, as⟩, fun h =>
          let ⟨s, h, as⟩ := F.mem_nhds.1 h
          ⟨⟨s, h⟩, as⟩⟩⟩
#align ctop.realizer.nhds Ctop.Realizer.nhds
-/

/- warning: ctop.realizer.nhds_σ -> Ctop.Realizer.nhds_σ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (F : Ctop.Realizer.{u1, u2} α _inst_1) (a : α), Eq.{succ (succ u2)} Type.{u2} (Filter.Realizer.σ.{u1, u2} α (nhds.{u1} α _inst_1 a) (Ctop.Realizer.nhds.{u1, u2} α _inst_1 F a)) (Subtype.{succ u2} (Ctop.Realizer.σ.{u1, u2} α _inst_1 F) (fun (s : Ctop.Realizer.σ.{u1, u2} α _inst_1 F) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (fun (_x : Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) => (Ctop.Realizer.σ.{u1, u2} α _inst_1 F) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (Ctop.Realizer.f.{u1, u2} α _inst_1 F) s)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] (F : Ctop.Realizer.{u2, u1} α _inst_1) (a : α), Eq.{succ (succ u1)} Type.{u1} (Filter.Realizer.σ.{u2, u1} α (nhds.{u2} α _inst_1 a) (Ctop.Realizer.nhds.{u2, u1} α _inst_1 F a)) (Subtype.{succ u1} (Ctop.Realizer.σ.{u2, u1} α _inst_1 F) (fun (s : Ctop.Realizer.σ.{u2, u1} α _inst_1 F) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Ctop.f.{u2, u1} α (Ctop.Realizer.σ.{u2, u1} α _inst_1 F) (Ctop.Realizer.F.{u2, u1} α _inst_1 F) s)))
Case conversion may be inaccurate. Consider using '#align ctop.realizer.nhds_σ Ctop.Realizer.nhds_σₓ'. -/
@[simp]
theorem nhds_σ (F : Realizer α) (a : α) : (F.nhds a).σ = { s : F.σ // a ∈ F.f s } :=
  rfl
#align ctop.realizer.nhds_σ Ctop.Realizer.nhds_σ

/- warning: ctop.realizer.nhds_F -> Ctop.Realizer.nhds_F is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (F : Ctop.Realizer.{u1, u2} α _inst_1) (a : α) (s : Filter.Realizer.σ.{u1, u2} α (nhds.{u1} α _inst_1 a) (Ctop.Realizer.nhds.{u1, u2} α _inst_1 F a)), Eq.{succ u1} (Set.{u1} α) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (CFilter.{u1, u2} (Set.{u1} α) (Filter.Realizer.σ.{u1, u2} α (nhds.{u1} α _inst_1 a) (Ctop.Realizer.nhds.{u1, u2} α _inst_1 F a)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (fun (_x : CFilter.{u1, u2} (Set.{u1} α) (Filter.Realizer.σ.{u1, u2} α (nhds.{u1} α _inst_1 a) (Ctop.Realizer.nhds.{u1, u2} α _inst_1 F a)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) => (Filter.Realizer.σ.{u1, u2} α (nhds.{u1} α _inst_1 a) (Ctop.Realizer.nhds.{u1, u2} α _inst_1 F a)) -> (Set.{u1} α)) (CFilter.hasCoeToFun.{u1, u2} (Set.{u1} α) (Filter.Realizer.σ.{u1, u2} α (nhds.{u1} α _inst_1 a) (Ctop.Realizer.nhds.{u1, u2} α _inst_1 F a)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (Filter.Realizer.f.{u1, u2} α (nhds.{u1} α _inst_1 a) (Ctop.Realizer.nhds.{u1, u2} α _inst_1 F a)) s) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (fun (_x : Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) => (Ctop.Realizer.σ.{u1, u2} α _inst_1 F) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (Ctop.Realizer.f.{u1, u2} α _inst_1 F) (Subtype.val.{succ u2} (Ctop.Realizer.σ.{u1, u2} α _inst_1 F) (fun (s : Ctop.Realizer.σ.{u1, u2} α _inst_1 F) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (fun (_x : Ctop.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) => (Ctop.Realizer.σ.{u1, u2} α _inst_1 F) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u2} α (Ctop.Realizer.σ.{u1, u2} α _inst_1 F)) (Ctop.Realizer.f.{u1, u2} α _inst_1 F) s)) s))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] (F : Ctop.Realizer.{u2, u1} α _inst_1) (a : α) (s : Filter.Realizer.σ.{u2, u1} α (nhds.{u2} α _inst_1 a) (Ctop.Realizer.nhds.{u2, u1} α _inst_1 F a)), Eq.{succ u2} (Set.{u2} α) (CFilter.f.{u2, u1} (Set.{u2} α) (Filter.Realizer.σ.{u2, u1} α (nhds.{u2} α _inst_1 a) (Ctop.Realizer.nhds.{u2, u1} α _inst_1 F a)) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (Filter.Realizer.F.{u2, u1} α (nhds.{u2} α _inst_1 a) (Ctop.Realizer.nhds.{u2, u1} α _inst_1 F a)) s) (Ctop.f.{u2, u1} α (Ctop.Realizer.σ.{u2, u1} α _inst_1 F) (Ctop.Realizer.F.{u2, u1} α _inst_1 F) (Subtype.val.{succ u1} (Ctop.Realizer.σ.{u2, u1} α _inst_1 F) (fun (s : Ctop.Realizer.σ.{u2, u1} α _inst_1 F) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Ctop.f.{u2, u1} α (Ctop.Realizer.σ.{u2, u1} α _inst_1 F) (Ctop.Realizer.F.{u2, u1} α _inst_1 F) s)) s))
Case conversion may be inaccurate. Consider using '#align ctop.realizer.nhds_F Ctop.Realizer.nhds_Fₓ'. -/
@[simp]
theorem nhds_F (F : Realizer α) (a : α) (s) : (F.nhds a).f s = F.f s.1 :=
  rfl
#align ctop.realizer.nhds_F Ctop.Realizer.nhds_F

/- warning: ctop.realizer.tendsto_nhds_iff -> Ctop.Realizer.tendsto_nhds_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {m : β -> α} {f : Filter.{u2} β} (F : Filter.Realizer.{u2, u3} β f) (R : Ctop.Realizer.{u1, u4} α _inst_1) {a : α}, Iff (Filter.Tendsto.{u2, u1} β α m f (nhds.{u1} α _inst_1 a)) (forall (t : Ctop.Realizer.σ.{u1, u4} α _inst_1 R), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (coeFn.{max (succ u1) (succ u4), max (succ u4) (succ u1)} (Ctop.{u1, u4} α (Ctop.Realizer.σ.{u1, u4} α _inst_1 R)) (fun (_x : Ctop.{u1, u4} α (Ctop.Realizer.σ.{u1, u4} α _inst_1 R)) => (Ctop.Realizer.σ.{u1, u4} α _inst_1 R) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u4} α (Ctop.Realizer.σ.{u1, u4} α _inst_1 R)) (Ctop.Realizer.f.{u1, u4} α _inst_1 R) t)) -> (Exists.{succ u3} (Filter.Realizer.σ.{u2, u3} β f F) (fun (s : Filter.Realizer.σ.{u2, u3} β f F) => forall (x : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (CFilter.{u2, u3} (Set.{u2} β) (Filter.Realizer.σ.{u2, u3} β f F) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (_x : CFilter.{u2, u3} (Set.{u2} β) (Filter.Realizer.σ.{u2, u3} β f F) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) => (Filter.Realizer.σ.{u2, u3} β f F) -> (Set.{u2} β)) (CFilter.hasCoeToFun.{u2, u3} (Set.{u2} β) (Filter.Realizer.σ.{u2, u3} β f F) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (Filter.Realizer.f.{u2, u3} β f F) s)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (m x) (coeFn.{max (succ u1) (succ u4), max (succ u4) (succ u1)} (Ctop.{u1, u4} α (Ctop.Realizer.σ.{u1, u4} α _inst_1 R)) (fun (_x : Ctop.{u1, u4} α (Ctop.Realizer.σ.{u1, u4} α _inst_1 R)) => (Ctop.Realizer.σ.{u1, u4} α _inst_1 R) -> (Set.{u1} α)) (Ctop.hasCoeToFun.{u1, u4} α (Ctop.Realizer.σ.{u1, u4} α _inst_1 R)) (Ctop.Realizer.f.{u1, u4} α _inst_1 R) t)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u4}} [_inst_1 : TopologicalSpace.{u2} α] {m : β -> α} {f : Filter.{u4} β} (F : Filter.Realizer.{u4, u3} β f) (R : Ctop.Realizer.{u2, u1} α _inst_1) {a : α}, Iff (Filter.Tendsto.{u4, u2} β α m f (nhds.{u2} α _inst_1 a)) (forall (t : Ctop.Realizer.σ.{u2, u1} α _inst_1 R), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Ctop.f.{u2, u1} α (Ctop.Realizer.σ.{u2, u1} α _inst_1 R) (Ctop.Realizer.F.{u2, u1} α _inst_1 R) t)) -> (Exists.{succ u3} (Filter.Realizer.σ.{u4, u3} β f F) (fun (s : Filter.Realizer.σ.{u4, u3} β f F) => forall (x : β), (Membership.mem.{u4, u4} β (Set.{u4} β) (Set.instMembershipSet.{u4} β) x (CFilter.f.{u4, u3} (Set.{u4} β) (Filter.Realizer.σ.{u4, u3} β f F) (CompleteSemilatticeInf.toPartialOrder.{u4} (Set.{u4} β) (CompleteLattice.toCompleteSemilatticeInf.{u4} (Set.{u4} β) (Order.Coframe.toCompleteLattice.{u4} (Set.{u4} β) (CompleteDistribLattice.toCoframe.{u4} (Set.{u4} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u4} (Set.{u4} β) (Set.instCompleteBooleanAlgebraSet.{u4} β)))))) (Filter.Realizer.F.{u4, u3} β f F) s)) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (m x) (Ctop.f.{u2, u1} α (Ctop.Realizer.σ.{u2, u1} α _inst_1 R) (Ctop.Realizer.F.{u2, u1} α _inst_1 R) t)))))
Case conversion may be inaccurate. Consider using '#align ctop.realizer.tendsto_nhds_iff Ctop.Realizer.tendsto_nhds_iffₓ'. -/
theorem tendsto_nhds_iff {m : β → α} {f : Filter β} (F : f.Realizer) (R : Realizer α) {a : α} :
    Tendsto m f (𝓝 a) ↔ ∀ t, a ∈ R.f t → ∃ s, ∀ x ∈ F.f s, m x ∈ R.f t :=
  (F.tendsto_iffₓ _ (R.nhds a)).trans Subtype.forall
#align ctop.realizer.tendsto_nhds_iff Ctop.Realizer.tendsto_nhds_iff

end Ctop.Realizer

#print LocallyFinite.Realizer /-
/-- A `locally_finite.realizer F f` is a realization that `f` is locally finite, namely it is a
choice of open sets from the basis of `F` such that they intersect only finitely many of the values
of `f`.  -/
structure LocallyFinite.Realizer [TopologicalSpace α] (F : Realizer α) (f : β → Set α) where
  bas : ∀ a, { s // a ∈ F.f s }
  sets : ∀ x : α, Fintype { i | (f i ∩ F.f (bas x)).Nonempty }
#align locally_finite.realizer LocallyFinite.Realizer
-/

/- warning: locally_finite.realizer.to_locally_finite -> LocallyFinite.Realizer.to_locallyFinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {F : Ctop.Realizer.{u1, u3} α _inst_1} {f : β -> (Set.{u1} α)}, (LocallyFinite.Realizer.{u1, u2, u3} α β _inst_1 F f) -> (LocallyFinite.{u2, u1} β α _inst_1 f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] {F : Ctop.Realizer.{u3, u2} α _inst_1} {f : β -> (Set.{u3} α)}, (LocallyFinite.Realizer.{u3, u1, u2} α β _inst_1 F f) -> (LocallyFinite.{u1, u3} β α _inst_1 f)
Case conversion may be inaccurate. Consider using '#align locally_finite.realizer.to_locally_finite LocallyFinite.Realizer.to_locallyFiniteₓ'. -/
theorem LocallyFinite.Realizer.to_locallyFinite [TopologicalSpace α] {F : Realizer α}
    {f : β → Set α} (R : LocallyFinite.Realizer F f) : LocallyFinite f := fun a =>
  ⟨_, F.mem_nhds.2 ⟨(R.bas a).1, (R.bas a).2, Subset.refl _⟩, ⟨R.sets a⟩⟩
#align locally_finite.realizer.to_locally_finite LocallyFinite.Realizer.to_locallyFinite

/- warning: locally_finite_iff_exists_realizer -> locallyFinite_iff_exists_realizer is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] (F : Ctop.Realizer.{u1, u3} α _inst_1) {f : β -> (Set.{u1} α)}, Iff (LocallyFinite.{u2, u1} β α _inst_1 f) (Nonempty.{max (succ u1) (succ u2) (succ u3)} (LocallyFinite.Realizer.{u1, u2, u3} α β _inst_1 F f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] (F : Ctop.Realizer.{u3, u2} α _inst_1) {f : β -> (Set.{u3} α)}, Iff (LocallyFinite.{u1, u3} β α _inst_1 f) (Nonempty.{max (max (succ u2) (succ u1)) (succ u3)} (LocallyFinite.Realizer.{u3, u1, u2} α β _inst_1 F f))
Case conversion may be inaccurate. Consider using '#align locally_finite_iff_exists_realizer locallyFinite_iff_exists_realizerₓ'. -/
theorem locallyFinite_iff_exists_realizer [TopologicalSpace α] (F : Realizer α) {f : β → Set α} :
    LocallyFinite f ↔ Nonempty (LocallyFinite.Realizer F f) :=
  ⟨fun h =>
    let ⟨g, h₁⟩ := Classical.axiom_of_choice h
    let ⟨g₂, h₂⟩ :=
      Classical.axiom_of_choice fun x =>
        show ∃ b : F.σ, x ∈ F.f b ∧ F.f b ⊆ g x from
          let ⟨h, h'⟩ := h₁ x
          F.mem_nhds.1 h
    ⟨⟨fun x => ⟨g₂ x, (h₂ x).1⟩, fun x =>
        Finite.fintype <|
          let ⟨h, h'⟩ := h₁ x
          h'.Subset fun i hi => hi.mono (inter_subset_inter_right _ (h₂ x).2)⟩⟩,
    fun ⟨R⟩ => R.to_locallyFinite⟩
#align locally_finite_iff_exists_realizer locallyFinite_iff_exists_realizer

instance [TopologicalSpace α] [Finite β] (F : Realizer α) (f : β → Set α) :
    Nonempty (LocallyFinite.Realizer F f) :=
  (locallyFinite_iff_exists_realizer _).1 <| locallyFinite_of_finite _

#print Compact.Realizer /-
/-- A `compact.realizer s` is a realization that `s` is compact, namely it is a
choice of finite open covers for each set family covering `s`.  -/
def Compact.Realizer [TopologicalSpace α] (s : Set α) :=
  ∀ {f : Filter α} (F : f.Realizer) (x : F.σ), f ≠ ⊥ → F.f x ⊆ s → { a // a ∈ s ∧ 𝓝 a ⊓ f ≠ ⊥ }
#align compact.realizer Compact.Realizer
-/

instance [TopologicalSpace α] : Inhabited (Compact.Realizer (∅ : Set α)) :=
  ⟨fun f F x h hF => by
    cases h _
    rw [← F.eq, eq_bot_iff]
    exact fun s _ => ⟨x, hF.trans s.empty_subset⟩⟩

