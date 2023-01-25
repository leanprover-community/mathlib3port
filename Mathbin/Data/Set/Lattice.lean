/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.set.lattice
! leanprover-community/mathlib commit e3d9ab8faa9dea8f78155c6c27d62a621f4c152d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.CompleteBooleanAlgebra
import Mathbin.Order.Directed
import Mathbin.Order.GaloisConnection

/-!
# The set lattice

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides usual set notation for unions and intersections, a `complete_lattice` instance
for `set α`, and some more set constructions.

## Main declarations

* `set.Union`: Union of an indexed family of sets.
* `set.Inter`: Intersection of an indexed family of sets.
* `set.sInter`: **s**et **Inter**. Intersection of sets belonging to a set of sets.
* `set.sUnion`: **s**et **Union**. Union of sets belonging to a set of sets. This is actually
  defined in core Lean.
* `set.sInter_eq_bInter`, `set.sUnion_eq_bInter`: Shows that `⋂₀ s = ⋂ x ∈ s, x` and
  `⋃₀ s = ⋃ x ∈ s, x`.
* `set.complete_boolean_algebra`: `set α` is a `complete_boolean_algebra` with `≤ = ⊆`, `< = ⊂`,
  `⊓ = ∩`, `⊔ = ∪`, `⨅ = ⋂`, `⨆ = ⋃` and `\` as the set difference. See `set.boolean_algebra`.
* `set.kern_image`: For a function `f : α → β`, `s.kern_image f` is the set of `y` such that
  `f ⁻¹ y ⊆ s`.
* `set.seq`: Union of the image of a set under a **seq**uence of functions. `seq s t` is the union
  of `f '' t` over all `f ∈ s`, where `t : set α` and `s : set (α → β)`.
* `set.Union_eq_sigma_of_disjoint`: Equivalence between `⋃ i, t i` and `Σ i, t i`, where `t` is an
  indexed family of disjoint sets.

## Naming convention

In lemma names,
* `⋃ i, s i` is called `Union`
* `⋂ i, s i` is called `Inter`
* `⋃ i j, s i j` is called `Union₂`. This is a `Union` inside a `Union`.
* `⋂ i j, s i j` is called `Inter₂`. This is an `Inter` inside an `Inter`.
* `⋃ i ∈ s, t i` is called `bUnion` for "bounded `Union`". This is the special case of `Union₂`
  where `j : i ∈ s`.
* `⋂ i ∈ s, t i` is called `bInter` for "bounded `Inter`". This is the special case of `Inter₂`
  where `j : i ∈ s`.

## Notation

* `⋃`: `set.Union`
* `⋂`: `set.Inter`
* `⋃₀`: `set.sUnion`
* `⋂₀`: `set.sInter`
-/


open Function Tactic Set

universe u

variable {α β γ : Type _} {ι ι' ι₂ : Sort _} {κ κ₁ κ₂ : ι → Sort _} {κ' : ι' → Sort _}

namespace Set

/-! ### Complete lattice and complete Boolean algebra instances -/


instance : InfSet (Set α) :=
  ⟨fun s => { a | ∀ t ∈ s, a ∈ t }⟩

instance : SupSet (Set α) :=
  ⟨fun s => { a | ∃ t ∈ s, a ∈ t }⟩

#print Set.interₛ /-
/-- Intersection of a set of sets. -/
def interₛ (S : Set (Set α)) : Set α :=
  infₛ S
#align set.sInter Set.interₛ
-/

#print Set.unionₛ /-
/-- Union of a set of sets. -/
def unionₛ (S : Set (Set α)) : Set α :=
  supₛ S
#align set.sUnion Set.unionₛ
-/

-- mathport name: «expr⋂₀ »
prefix:110 "⋂₀ " => interₛ

#print Set.mem_interₛ /-
@[simp]
theorem mem_interₛ {x : α} {S : Set (Set α)} : x ∈ ⋂₀ S ↔ ∀ t ∈ S, x ∈ t :=
  Iff.rfl
#align set.mem_sInter Set.mem_interₛ
-/

/- warning: set.mem_sUnion -> Set.mem_unionₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : α} {S : Set.{u1} (Set.{u1} α)}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.unionₛ.{u1} α S)) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t S) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t S) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t)))
but is expected to have type
  forall {α : Type.{u1}} {x : α} {S : Set.{u1} (Set.{u1} α)}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.unionₛ.{u1} α S)) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) t S) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t)))
Case conversion may be inaccurate. Consider using '#align set.mem_sUnion Set.mem_unionₛₓ'. -/
@[simp]
theorem mem_unionₛ {x : α} {S : Set (Set α)} : x ∈ ⋃₀ S ↔ ∃ t ∈ S, x ∈ t :=
  Iff.rfl
#align set.mem_sUnion Set.mem_unionₛ

#print Set.unionᵢ /-
/-- Indexed union of a family of sets -/
def unionᵢ (s : ι → Set β) : Set β :=
  supᵢ s
#align set.Union Set.unionᵢ
-/

#print Set.interᵢ /-
/-- Indexed intersection of a family of sets -/
def interᵢ (s : ι → Set β) : Set β :=
  infᵢ s
#align set.Inter Set.interᵢ
-/

-- mathport name: «expr⋃ , »
notation3"⋃ "(...)", "r:(scoped f => unionᵢ f) => r

-- mathport name: «expr⋂ , »
notation3"⋂ "(...)", "r:(scoped f => interᵢ f) => r

/- warning: set.Sup_eq_sUnion -> Set.supₛ_eq_unionₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (SupSet.supₛ.{u1} (Set.{u1} α) (Set.hasSup.{u1} α) S) (Set.unionₛ.{u1} α S)
but is expected to have type
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (SupSet.supₛ.{u1} (Set.{u1} α) (Set.instSupSetSet.{u1} α) S) (Set.unionₛ.{u1} α S)
Case conversion may be inaccurate. Consider using '#align set.Sup_eq_sUnion Set.supₛ_eq_unionₛₓ'. -/
@[simp]
theorem supₛ_eq_unionₛ (S : Set (Set α)) : supₛ S = ⋃₀ S :=
  rfl
#align set.Sup_eq_sUnion Set.supₛ_eq_unionₛ

#print Set.infₛ_eq_interₛ /-
@[simp]
theorem infₛ_eq_interₛ (S : Set (Set α)) : infₛ S = ⋂₀ S :=
  rfl
#align set.Inf_eq_sInter Set.infₛ_eq_interₛ
-/

/- warning: set.supr_eq_Union -> Set.supᵢ_eq_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (supᵢ.{u1, u2} (Set.{u1} α) (Set.hasSup.{u1} α) ι s) (Set.unionᵢ.{u1, u2} α ι s)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (supᵢ.{u2, u1} (Set.{u2} α) (Set.instSupSetSet.{u2} α) ι s) (Set.unionᵢ.{u2, u1} α ι s)
Case conversion may be inaccurate. Consider using '#align set.supr_eq_Union Set.supᵢ_eq_unionᵢₓ'. -/
@[simp]
theorem supᵢ_eq_unionᵢ (s : ι → Set α) : supᵢ s = unionᵢ s :=
  rfl
#align set.supr_eq_Union Set.supᵢ_eq_unionᵢ

/- warning: set.infi_eq_Inter -> Set.infᵢ_eq_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (infᵢ.{u1, u2} (Set.{u1} α) (Set.hasInf.{u1} α) ι s) (Set.interᵢ.{u1, u2} α ι s)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (infᵢ.{u2, u1} (Set.{u2} α) (Set.instInfSetSet.{u2} α) ι s) (Set.interᵢ.{u2, u1} α ι s)
Case conversion may be inaccurate. Consider using '#align set.infi_eq_Inter Set.infᵢ_eq_interᵢₓ'. -/
@[simp]
theorem infᵢ_eq_interᵢ (s : ι → Set α) : infᵢ s = interᵢ s :=
  rfl
#align set.infi_eq_Inter Set.infᵢ_eq_interᵢ

/- warning: set.mem_Union -> Set.mem_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {x : α} {s : ι -> (Set.{u1} α)}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i))) (Exists.{u2} ι (fun (i : ι) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {x : α} {s : ι -> (Set.{u2} α)}, Iff (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i))) (Exists.{u1} ι (fun (i : ι) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (s i)))
Case conversion may be inaccurate. Consider using '#align set.mem_Union Set.mem_unionᵢₓ'. -/
@[simp]
theorem mem_unionᵢ {x : α} {s : ι → Set α} : (x ∈ ⋃ i, s i) ↔ ∃ i, x ∈ s i :=
  ⟨fun ⟨t, ⟨⟨a, (t_eq : s a = t)⟩, (h : x ∈ t)⟩⟩ => ⟨a, t_eq.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩
#align set.mem_Union Set.mem_unionᵢ

/- warning: set.mem_Inter -> Set.mem_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {x : α} {s : ι -> (Set.{u1} α)}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i))) (forall (i : ι), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {x : α} {s : ι -> (Set.{u2} α)}, Iff (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => s i))) (forall (i : ι), Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (s i))
Case conversion may be inaccurate. Consider using '#align set.mem_Inter Set.mem_interᵢₓ'. -/
@[simp]
theorem mem_interᵢ {x : α} {s : ι → Set α} : (x ∈ ⋂ i, s i) ↔ ∀ i, x ∈ s i :=
  ⟨fun (h : ∀ a ∈ { a : Set α | ∃ i, s i = a }, x ∈ a) a => h (s a) ⟨a, rfl⟩,
    fun h t ⟨a, (Eq : s a = t)⟩ => Eq ▸ h a⟩
#align set.mem_Inter Set.mem_interᵢ

/- warning: set.mem_Union₂ -> Set.mem_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {x : γ} {s : forall (i : ι), (κ i) -> (Set.{u1} γ)}, Iff (Membership.Mem.{u1, u1} γ (Set.{u1} γ) (Set.hasMem.{u1} γ) x (Set.unionᵢ.{u1, u2} γ ι (fun (i : ι) => Set.unionᵢ.{u1, u3} γ (κ i) (fun (j : κ i) => s i j)))) (Exists.{u2} ι (fun (i : ι) => Exists.{u3} (κ i) (fun (j : κ i) => Membership.Mem.{u1, u1} γ (Set.{u1} γ) (Set.hasMem.{u1} γ) x (s i j))))
but is expected to have type
  forall {γ : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {x : γ} {s : forall (i : ι), (κ i) -> (Set.{u3} γ)}, Iff (Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) x (Set.unionᵢ.{u3, u2} γ ι (fun (i : ι) => Set.unionᵢ.{u3, u1} γ (κ i) (fun (j : κ i) => s i j)))) (Exists.{u2} ι (fun (i : ι) => Exists.{u1} (κ i) (fun (j : κ i) => Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) x (s i j))))
Case conversion may be inaccurate. Consider using '#align set.mem_Union₂ Set.mem_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mem_unionᵢ₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋃ (i) (j), s i j) ↔ ∃ i j, x ∈ s i j := by
  simp_rw [mem_Union]
#align set.mem_Union₂ Set.mem_unionᵢ₂

/- warning: set.mem_Inter₂ -> Set.mem_interᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {x : γ} {s : forall (i : ι), (κ i) -> (Set.{u1} γ)}, Iff (Membership.Mem.{u1, u1} γ (Set.{u1} γ) (Set.hasMem.{u1} γ) x (Set.interᵢ.{u1, u2} γ ι (fun (i : ι) => Set.interᵢ.{u1, u3} γ (κ i) (fun (j : κ i) => s i j)))) (forall (i : ι) (j : κ i), Membership.Mem.{u1, u1} γ (Set.{u1} γ) (Set.hasMem.{u1} γ) x (s i j))
but is expected to have type
  forall {γ : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {x : γ} {s : forall (i : ι), (κ i) -> (Set.{u3} γ)}, Iff (Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) x (Set.interᵢ.{u3, u2} γ ι (fun (i : ι) => Set.interᵢ.{u3, u1} γ (κ i) (fun (j : κ i) => s i j)))) (forall (i : ι) (j : κ i), Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) x (s i j))
Case conversion may be inaccurate. Consider using '#align set.mem_Inter₂ Set.mem_interᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mem_interᵢ₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋂ (i) (j), s i j) ↔ ∀ i j, x ∈ s i j := by
  simp_rw [mem_Inter]
#align set.mem_Inter₂ Set.mem_interᵢ₂

/- warning: set.mem_Union_of_mem -> Set.mem_unionᵢ_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)} {a : α} (i : ι), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (s i)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u2} α)} {a : α} (i : ι), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (s i)) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i)))
Case conversion may be inaccurate. Consider using '#align set.mem_Union_of_mem Set.mem_unionᵢ_of_memₓ'. -/
theorem mem_unionᵢ_of_mem {s : ι → Set α} {a : α} (i : ι) (ha : a ∈ s i) : a ∈ ⋃ i, s i :=
  mem_unionᵢ.2 ⟨i, ha⟩
#align set.mem_Union_of_mem Set.mem_unionᵢ_of_mem

/- warning: set.mem_Union₂_of_mem -> Set.mem_unionᵢ₂_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {a : α} {i : ι} (j : κ i), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (s i j)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u3} α)} {a : α} {i : ι} (j : κ i), (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (s i j)) -> (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))))
Case conversion may be inaccurate. Consider using '#align set.mem_Union₂_of_mem Set.mem_unionᵢ₂_of_memₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mem_unionᵢ₂_of_mem {s : ∀ i, κ i → Set α} {a : α} {i : ι} (j : κ i) (ha : a ∈ s i j) :
    a ∈ ⋃ (i) (j), s i j :=
  mem_unionᵢ₂.2 ⟨i, j, ha⟩
#align set.mem_Union₂_of_mem Set.mem_unionᵢ₂_of_mem

/- warning: set.mem_Inter_of_mem -> Set.mem_interᵢ_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)} {a : α}, (forall (i : ι), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (s i)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u2} α)} {a : α}, (forall (i : ι), Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (s i)) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => s i)))
Case conversion may be inaccurate. Consider using '#align set.mem_Inter_of_mem Set.mem_interᵢ_of_memₓ'. -/
theorem mem_interᵢ_of_mem {s : ι → Set α} {a : α} (h : ∀ i, a ∈ s i) : a ∈ ⋂ i, s i :=
  mem_interᵢ.2 h
#align set.mem_Inter_of_mem Set.mem_interᵢ_of_mem

/- warning: set.mem_Inter₂_of_mem -> Set.mem_interᵢ₂_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {a : α}, (forall (i : ι) (j : κ i), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (s i j)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u3} α)} {a : α}, (forall (i : ι) (j : κ i), Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (s i j)) -> (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))))
Case conversion may be inaccurate. Consider using '#align set.mem_Inter₂_of_mem Set.mem_interᵢ₂_of_memₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mem_interᵢ₂_of_mem {s : ∀ i, κ i → Set α} {a : α} (h : ∀ i j, a ∈ s i j) :
    a ∈ ⋂ (i) (j), s i j :=
  mem_interᵢ₂.2 h
#align set.mem_Inter₂_of_mem Set.mem_interᵢ₂_of_mem

instance : CompleteBooleanAlgebra (Set α) :=
  { Set.booleanAlgebra with
    sup := supₛ
    inf := infₛ
    le_Sup := fun s t t_in a a_in => ⟨t, ⟨t_in, a_in⟩⟩
    Sup_le := fun s t h a ⟨t', ⟨t'_in, a_in⟩⟩ => h t' t'_in a_in
    le_Inf := fun s t h a a_in t' t'_in => h t' t'_in a_in
    Inf_le := fun s t t_in a h => h _ t_in
    infi_sup_le_sup_Inf := fun s S x => Iff.mp <| by simp [forall_or_left]
    inf_Sup_le_supr_inf := fun s S x => Iff.mp <| by simp [exists_and_left] }

section GaloisConnection

variable {f : α → β}

/- warning: set.image_preimage -> Set.image_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, GaloisConnection.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (Set.image.{u1, u2} α β f) (Set.preimage.{u1, u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, GaloisConnection.{u2, u1} (Set.{u2} α) (Set.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (Set.image.{u2, u1} α β f) (Set.preimage.{u2, u1} α β f)
Case conversion may be inaccurate. Consider using '#align set.image_preimage Set.image_preimageₓ'. -/
protected theorem image_preimage : GaloisConnection (image f) (preimage f) := fun a b =>
  image_subset_iff
#align set.image_preimage Set.image_preimage

#print Set.kernImage /-
/-- `kern_image f s` is the set of `y` such that `f ⁻¹ y ⊆ s`. -/
def kernImage (f : α → β) (s : Set α) : Set β :=
  { y | ∀ ⦃x⦄, f x = y → x ∈ s }
#align set.kern_image Set.kernImage
-/

/- warning: set.preimage_kern_image -> Set.preimage_kernImage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, GaloisConnection.{u2, u1} (Set.{u2} β) (Set.{u1} α) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (Set.preimage.{u1, u2} α β f) (Set.kernImage.{u1, u2} α β f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, GaloisConnection.{u2, u1} (Set.{u2} β) (Set.{u1} α) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (Set.preimage.{u1, u2} α β f) (Set.kernImage.{u1, u2} α β f)
Case conversion may be inaccurate. Consider using '#align set.preimage_kern_image Set.preimage_kernImageₓ'. -/
protected theorem preimage_kernImage : GaloisConnection (preimage f) (kernImage f) := fun a b =>
  ⟨fun h x hx y hy =>
    have : f y ∈ a := hy.symm ▸ hx
    h this,
    fun h x (hx : f x ∈ a) => h hx rfl⟩
#align set.preimage_kern_image Set.preimage_kernImage

end GaloisConnection

/-! ### Union and intersection over an indexed family of sets -/


instance : OrderTop (Set α) where
  top := univ
  le_top := by simp

#print Set.unionᵢ_congr_Prop /-
@[congr]
theorem unionᵢ_congr_Prop {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : unionᵢ f₁ = unionᵢ f₂ :=
  supᵢ_congr_Prop pq f
#align set.Union_congr_Prop Set.unionᵢ_congr_Prop
-/

#print Set.interᵢ_congr_Prop /-
@[congr]
theorem interᵢ_congr_Prop {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : interᵢ f₁ = interᵢ f₂ :=
  infᵢ_congr_Prop pq f
#align set.Inter_congr_Prop Set.interᵢ_congr_Prop
-/

#print Set.unionᵢ_plift_up /-
theorem unionᵢ_plift_up (f : PLift ι → Set α) : (⋃ i, f (PLift.up i)) = ⋃ i, f i :=
  supᵢ_plift_up _
#align set.Union_plift_up Set.unionᵢ_plift_up
-/

/- warning: set.Union_plift_down -> Set.unionᵢ_plift_down is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α (PLift.{u2} ι) (fun (i : PLift.{u2} ι) => f (PLift.down.{u2} ι i))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (f : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, succ u1} α (PLift.{u1} ι) (fun (i : PLift.{u1} ι) => f (PLift.down.{u1} ι i))) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align set.Union_plift_down Set.unionᵢ_plift_downₓ'. -/
theorem unionᵢ_plift_down (f : ι → Set α) : (⋃ i, f (PLift.down i)) = ⋃ i, f i :=
  supᵢ_plift_down _
#align set.Union_plift_down Set.unionᵢ_plift_down

#print Set.interᵢ_plift_up /-
theorem interᵢ_plift_up (f : PLift ι → Set α) : (⋂ i, f (PLift.up i)) = ⋂ i, f i :=
  infᵢ_plift_up _
#align set.Inter_plift_up Set.interᵢ_plift_up
-/

/- warning: set.Inter_plift_down -> Set.interᵢ_plift_down is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, succ u2} α (PLift.{u2} ι) (fun (i : PLift.{u2} ι) => f (PLift.down.{u2} ι i))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (f : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Set.interᵢ.{u2, succ u1} α (PLift.{u1} ι) (fun (i : PLift.{u1} ι) => f (PLift.down.{u1} ι i))) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align set.Inter_plift_down Set.interᵢ_plift_downₓ'. -/
theorem interᵢ_plift_down (f : ι → Set α) : (⋂ i, f (PLift.down i)) = ⋂ i, f i :=
  infᵢ_plift_down _
#align set.Inter_plift_down Set.interᵢ_plift_down

#print Set.unionᵢ_eq_if /-
theorem unionᵢ_eq_if {p : Prop} [Decidable p] (s : Set α) : (⋃ h : p, s) = if p then s else ∅ :=
  supᵢ_eq_if _
#align set.Union_eq_if Set.unionᵢ_eq_if
-/

#print Set.unionᵢ_eq_dif /-
theorem unionᵢ_eq_dif {p : Prop} [Decidable p] (s : p → Set α) :
    (⋃ h : p, s h) = if h : p then s h else ∅ :=
  supᵢ_eq_dif _
#align set.Union_eq_dif Set.unionᵢ_eq_dif
-/

#print Set.interᵢ_eq_if /-
theorem interᵢ_eq_if {p : Prop} [Decidable p] (s : Set α) : (⋂ h : p, s) = if p then s else univ :=
  infᵢ_eq_if _
#align set.Inter_eq_if Set.interᵢ_eq_if
-/

#print Set.infᵢ_eq_dif /-
theorem infᵢ_eq_dif {p : Prop} [Decidable p] (s : p → Set α) :
    (⋂ h : p, s h) = if h : p then s h else univ :=
  infᵢ_eq_dif _
#align set.Infi_eq_dif Set.infᵢ_eq_dif
-/

/- warning: set.exists_set_mem_of_union_eq_top -> Set.exists_set_mem_of_union_eq_top is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Type.{u2}} (t : Set.{u2} ι) (s : ι -> (Set.{u1} β)), (Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, succ u2} β ι (fun (i : ι) => Set.unionᵢ.{u1, 0} β (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) => s i))) (Top.top.{u1} (Set.{u1} β) (CompleteLattice.toHasTop.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.completeBooleanAlgebra.{u1} β))))))) -> (forall (x : β), Exists.{succ u2} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) => Membership.Mem.{u1, u1} β (Set.{u1} β) (Set.hasMem.{u1} β) x (s i))))
but is expected to have type
  forall {β : Type.{u1}} {ι : Type.{u2}} (t : Set.{u2} ι) (s : ι -> (Set.{u1} β)), (Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, succ u2} β ι (fun (i : ι) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i t) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i t) => s i))) (Top.top.{u1} (Set.{u1} β) (CompleteLattice.toTop.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) -> (forall (x : β), Exists.{succ u2} ι (fun (i : ι) => And (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i t) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (s i))))
Case conversion may be inaccurate. Consider using '#align set.exists_set_mem_of_union_eq_top Set.exists_set_mem_of_union_eq_topₓ'. -/
theorem exists_set_mem_of_union_eq_top {ι : Type _} (t : Set ι) (s : ι → Set β)
    (w : (⋃ i ∈ t, s i) = ⊤) (x : β) : ∃ i ∈ t, x ∈ s i :=
  by
  have p : x ∈ ⊤ := Set.mem_univ x
  simpa only [← w, Set.mem_unionᵢ] using p
#align set.exists_set_mem_of_union_eq_top Set.exists_set_mem_of_union_eq_top

/- warning: set.nonempty_of_union_eq_top_of_nonempty -> Set.nonempty_of_union_eq_top_of_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (t : Set.{u2} ι) (s : ι -> (Set.{u1} α)), (Nonempty.{succ u1} α) -> (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i t) => s i))) (Top.top.{u1} (Set.{u1} α) (CompleteLattice.toHasTop.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) -> (Set.Nonempty.{u2} ι t)
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} (t : Set.{u2} ι) (s : ι -> (Set.{u1} α)), (Nonempty.{succ u1} α) -> (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i t) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i t) => s i))) (Top.top.{u1} (Set.{u1} α) (CompleteLattice.toTop.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) -> (Set.Nonempty.{u2} ι t)
Case conversion may be inaccurate. Consider using '#align set.nonempty_of_union_eq_top_of_nonempty Set.nonempty_of_union_eq_top_of_nonemptyₓ'. -/
theorem nonempty_of_union_eq_top_of_nonempty {ι : Type _} (t : Set ι) (s : ι → Set α)
    (H : Nonempty α) (w : (⋃ i ∈ t, s i) = ⊤) : t.Nonempty :=
  by
  obtain ⟨x, m, -⟩ := exists_set_mem_of_union_eq_top t s w H.some
  exact ⟨x, m⟩
#align set.nonempty_of_union_eq_top_of_nonempty Set.nonempty_of_union_eq_top_of_nonempty

/- warning: set.set_of_exists -> Set.setOf_exists is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (p : ι -> β -> Prop), Eq.{succ u1} (Set.{u1} β) (setOf.{u1} β (fun (x : β) => Exists.{u2} ι (fun (i : ι) => p i x))) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => setOf.{u1} β (fun (x : β) => p i x)))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (p : ι -> β -> Prop), Eq.{succ u2} (Set.{u2} β) (setOf.{u2} β (fun (x : β) => Exists.{u1} ι (fun (i : ι) => p i x))) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => setOf.{u2} β (fun (x : β) => p i x)))
Case conversion may be inaccurate. Consider using '#align set.set_of_exists Set.setOf_existsₓ'. -/
theorem setOf_exists (p : ι → β → Prop) : { x | ∃ i, p i x } = ⋃ i, { x | p i x } :=
  ext fun i => mem_unionᵢ.symm
#align set.set_of_exists Set.setOf_exists

/- warning: set.set_of_forall -> Set.setOf_forall is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (p : ι -> β -> Prop), Eq.{succ u1} (Set.{u1} β) (setOf.{u1} β (fun (x : β) => forall (i : ι), p i x)) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => setOf.{u1} β (fun (x : β) => p i x)))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (p : ι -> β -> Prop), Eq.{succ u2} (Set.{u2} β) (setOf.{u2} β (fun (x : β) => forall (i : ι), p i x)) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => setOf.{u2} β (fun (x : β) => p i x)))
Case conversion may be inaccurate. Consider using '#align set.set_of_forall Set.setOf_forallₓ'. -/
theorem setOf_forall (p : ι → β → Prop) : { x | ∀ i, p i x } = ⋂ i, { x | p i x } :=
  ext fun i => mem_interᵢ.symm
#align set.set_of_forall Set.setOf_forall

/- warning: set.Union_subset -> Set.unionᵢ_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)} {t : Set.{u1} α}, (forall (i : ι), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i) t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) t)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u2} α)} {t : Set.{u2} α}, (forall (i : ι), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (s i) t) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i)) t)
Case conversion may be inaccurate. Consider using '#align set.Union_subset Set.unionᵢ_subsetₓ'. -/
theorem unionᵢ_subset {s : ι → Set α} {t : Set α} (h : ∀ i, s i ⊆ t) : (⋃ i, s i) ⊆ t :=
  @supᵢ_le (Set α) _ _ _ _ h
#align set.Union_subset Set.unionᵢ_subset

/- warning: set.Union₂_subset -> Set.unionᵢ₂_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {t : Set.{u1} α}, (forall (i : ι) (j : κ i), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i j) t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) t)
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u3} α)} {t : Set.{u3} α}, (forall (i : ι) (j : κ i), HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (s i j) t) -> (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) t)
Case conversion may be inaccurate. Consider using '#align set.Union₂_subset Set.unionᵢ₂_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem unionᵢ₂_subset {s : ∀ i, κ i → Set α} {t : Set α} (h : ∀ i j, s i j ⊆ t) :
    (⋃ (i) (j), s i j) ⊆ t :=
  Union_subset fun x => unionᵢ_subset (h x)
#align set.Union₂_subset Set.unionᵢ₂_subset

/- warning: set.subset_Inter -> Set.subset_interᵢ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} {t : Set.{u1} β} {s : ι -> (Set.{u1} β)}, (forall (i : ι), HasSubset.Subset.{u1} (Set.{u1} β) (Set.hasSubset.{u1} β) t (s i)) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.hasSubset.{u1} β) t (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => s i)))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} {t : Set.{u2} β} {s : ι -> (Set.{u2} β)}, (forall (i : ι), HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) t (s i)) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) t (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => s i)))
Case conversion may be inaccurate. Consider using '#align set.subset_Inter Set.subset_interᵢₓ'. -/
theorem subset_interᵢ {t : Set β} {s : ι → Set β} (h : ∀ i, t ⊆ s i) : t ⊆ ⋂ i, s i :=
  @le_infᵢ (Set β) _ _ _ _ h
#align set.subset_Inter Set.subset_interᵢ

/- warning: set.subset_Inter₂ -> Set.subset_interᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : Set.{u1} α} {t : forall (i : ι), (κ i) -> (Set.{u1} α)}, (forall (i : ι) (j : κ i), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (t i j)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => t i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : Set.{u3} α} {t : forall (i : ι), (κ i) -> (Set.{u3} α)}, (forall (i : ι) (j : κ i), HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) s (t i j)) -> (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) s (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => t i j))))
Case conversion may be inaccurate. Consider using '#align set.subset_Inter₂ Set.subset_interᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem subset_interᵢ₂ {s : Set α} {t : ∀ i, κ i → Set α} (h : ∀ i j, s ⊆ t i j) :
    s ⊆ ⋂ (i) (j), t i j :=
  subset_Inter fun x => subset_Inter <| h x
#align set.subset_Inter₂ Set.subset_interᵢ₂

/- warning: set.Union_subset_iff -> Set.unionᵢ_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) t) (forall (i : ι), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i) t)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u2} α)} {t : Set.{u2} α}, Iff (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i)) t) (forall (i : ι), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (s i) t)
Case conversion may be inaccurate. Consider using '#align set.Union_subset_iff Set.unionᵢ_subset_iffₓ'. -/
@[simp]
theorem unionᵢ_subset_iff {s : ι → Set α} {t : Set α} : (⋃ i, s i) ⊆ t ↔ ∀ i, s i ⊆ t :=
  ⟨fun h i => Subset.trans (le_supᵢ s _) h, unionᵢ_subset⟩
#align set.Union_subset_iff Set.unionᵢ_subset_iff

/- warning: set.Union₂_subset_iff -> Set.unionᵢ₂_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) t) (forall (i : ι) (j : κ i), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i j) t)
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u3} α)} {t : Set.{u3} α}, Iff (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) t) (forall (i : ι) (j : κ i), HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (s i j) t)
Case conversion may be inaccurate. Consider using '#align set.Union₂_subset_iff Set.unionᵢ₂_subset_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem unionᵢ₂_subset_iff {s : ∀ i, κ i → Set α} {t : Set α} :
    (⋃ (i) (j), s i j) ⊆ t ↔ ∀ i j, s i j ⊆ t := by simp_rw [Union_subset_iff]
#align set.Union₂_subset_iff Set.unionᵢ₂_subset_iff

/- warning: set.subset_Inter_iff -> Set.subset_interᵢ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : Set.{u1} α} {t : ι -> (Set.{u1} α)}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => t i))) (forall (i : ι), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (t i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {s : Set.{u2} α} {t : ι -> (Set.{u2} α)}, Iff (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => t i))) (forall (i : ι), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (t i))
Case conversion may be inaccurate. Consider using '#align set.subset_Inter_iff Set.subset_interᵢ_iffₓ'. -/
@[simp]
theorem subset_interᵢ_iff {s : Set α} {t : ι → Set α} : (s ⊆ ⋂ i, t i) ↔ ∀ i, s ⊆ t i :=
  @le_infᵢ_iff (Set α) _ _ _ _
#align set.subset_Inter_iff Set.subset_interᵢ_iff

/- warning: set.subset_Inter₂_iff -> Set.subset_interᵢ₂_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : Set.{u1} α} {t : forall (i : ι), (κ i) -> (Set.{u1} α)}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => t i j)))) (forall (i : ι) (j : κ i), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (t i j))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : Set.{u3} α} {t : forall (i : ι), (κ i) -> (Set.{u3} α)}, Iff (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) s (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => t i j)))) (forall (i : ι) (j : κ i), HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) s (t i j))
Case conversion may be inaccurate. Consider using '#align set.subset_Inter₂_iff Set.subset_interᵢ₂_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem subset_interᵢ₂_iff {s : Set α} {t : ∀ i, κ i → Set α} :
    (s ⊆ ⋂ (i) (j), t i j) ↔ ∀ i j, s ⊆ t i j := by simp_rw [subset_Inter_iff]
#align set.subset_Inter₂_iff Set.subset_interᵢ₂_iff

/- warning: set.subset_Union -> Set.subset_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} β)) (i : ι), HasSubset.Subset.{u1} (Set.{u1} β) (Set.hasSubset.{u1} β) (s i) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => s i))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} β)) (i : ι), HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (s i) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => s i))
Case conversion may be inaccurate. Consider using '#align set.subset_Union Set.subset_unionᵢₓ'. -/
theorem subset_unionᵢ : ∀ (s : ι → Set β) (i : ι), s i ⊆ ⋃ i, s i :=
  le_supᵢ
#align set.subset_Union Set.subset_unionᵢ

/- warning: set.Inter_subset -> Set.interᵢ_subset is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} β)) (i : ι), HasSubset.Subset.{u1} (Set.{u1} β) (Set.hasSubset.{u1} β) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => s i)) (s i)
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} β)) (i : ι), HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => s i)) (s i)
Case conversion may be inaccurate. Consider using '#align set.Inter_subset Set.interᵢ_subsetₓ'. -/
theorem interᵢ_subset : ∀ (s : ι → Set β) (i : ι), (⋂ i, s i) ⊆ s i :=
  infᵢ_le
#align set.Inter_subset Set.interᵢ_subset

/- warning: set.subset_Union₂ -> Set.subset_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} (i : ι) (j : κ i), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i j) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u3} α)} (i : ι) (j : κ i), HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (s i j) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j)))
Case conversion may be inaccurate. Consider using '#align set.subset_Union₂ Set.subset_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem subset_unionᵢ₂ {s : ∀ i, κ i → Set α} (i : ι) (j : κ i) : s i j ⊆ ⋃ (i) (j), s i j :=
  @le_supᵢ₂ (Set α) _ _ _ _ i j
#align set.subset_Union₂ Set.subset_unionᵢ₂

/- warning: set.Inter₂_subset -> Set.interᵢ₂_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} (i : ι) (j : κ i), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) (s i j)
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u3} α)} (i : ι) (j : κ i), HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) (s i j)
Case conversion may be inaccurate. Consider using '#align set.Inter₂_subset Set.interᵢ₂_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem interᵢ₂_subset {s : ∀ i, κ i → Set α} (i : ι) (j : κ i) : (⋂ (i) (j), s i j) ⊆ s i j :=
  @infᵢ₂_le (Set α) _ _ _ _ i j
#align set.Inter₂_subset Set.interᵢ₂_subset

/- warning: set.subset_Union_of_subset -> Set.subset_unionᵢ_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : Set.{u1} α} {t : ι -> (Set.{u1} α)} (i : ι), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (t i)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => t i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {s : Set.{u2} α} {t : ι -> (Set.{u2} α)} (i : ι), (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (t i)) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.subset_Union_of_subset Set.subset_unionᵢ_of_subsetₓ'. -/
/-- This rather trivial consequence of `subset_Union`is convenient with `apply`, and has `i`
explicit for this purpose. -/
theorem subset_unionᵢ_of_subset {s : Set α} {t : ι → Set α} (i : ι) (h : s ⊆ t i) : s ⊆ ⋃ i, t i :=
  @le_supᵢ_of_le (Set α) _ _ _ _ i h
#align set.subset_Union_of_subset Set.subset_unionᵢ_of_subset

/- warning: set.Inter_subset_of_subset -> Set.interᵢ_subset_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)} {t : Set.{u1} α} (i : ι), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i) t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i)) t)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u2} α)} {t : Set.{u2} α} (i : ι), (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (s i) t) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => s i)) t)
Case conversion may be inaccurate. Consider using '#align set.Inter_subset_of_subset Set.interᵢ_subset_of_subsetₓ'. -/
/-- This rather trivial consequence of `Inter_subset`is convenient with `apply`, and has `i`
explicit for this purpose. -/
theorem interᵢ_subset_of_subset {s : ι → Set α} {t : Set α} (i : ι) (h : s i ⊆ t) :
    (⋂ i, s i) ⊆ t :=
  @infᵢ_le_of_le (Set α) _ _ _ _ i h
#align set.Inter_subset_of_subset Set.interᵢ_subset_of_subset

/- warning: set.subset_Union₂_of_subset -> Set.subset_unionᵢ₂_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : Set.{u1} α} {t : forall (i : ι), (κ i) -> (Set.{u1} α)} (i : ι) (j : κ i), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (t i j)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => t i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : Set.{u3} α} {t : forall (i : ι), (κ i) -> (Set.{u3} α)} (i : ι) (j : κ i), (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) s (t i j)) -> (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) s (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => t i j))))
Case conversion may be inaccurate. Consider using '#align set.subset_Union₂_of_subset Set.subset_unionᵢ₂_of_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- This rather trivial consequence of `subset_Union₂` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
theorem subset_unionᵢ₂_of_subset {s : Set α} {t : ∀ i, κ i → Set α} (i : ι) (j : κ i)
    (h : s ⊆ t i j) : s ⊆ ⋃ (i) (j), t i j :=
  @le_supᵢ₂_of_le (Set α) _ _ _ _ _ i j h
#align set.subset_Union₂_of_subset Set.subset_unionᵢ₂_of_subset

/- warning: set.Inter₂_subset_of_subset -> Set.interᵢ₂_subset_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {t : Set.{u1} α} (i : ι) (j : κ i), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i j) t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) t)
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u3} α)} {t : Set.{u3} α} (i : ι) (j : κ i), (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (s i j) t) -> (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) t)
Case conversion may be inaccurate. Consider using '#align set.Inter₂_subset_of_subset Set.interᵢ₂_subset_of_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- This rather trivial consequence of `Inter₂_subset` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
theorem interᵢ₂_subset_of_subset {s : ∀ i, κ i → Set α} {t : Set α} (i : ι) (j : κ i)
    (h : s i j ⊆ t) : (⋂ (i) (j), s i j) ⊆ t :=
  @infᵢ₂_le_of_le (Set α) _ _ _ _ _ i j h
#align set.Inter₂_subset_of_subset Set.interᵢ₂_subset_of_subset

/- warning: set.Union_mono -> Set.unionᵢ_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u1} α)}, (forall (i : ι), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i) (t i)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => t i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u2} α)}, (forall (i : ι), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (s i) (t i)) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.Union_mono Set.unionᵢ_monoₓ'. -/
theorem unionᵢ_mono {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : (⋃ i, s i) ⊆ ⋃ i, t i :=
  @supᵢ_mono (Set α) _ _ s t h
#align set.Union_mono Set.unionᵢ_mono

/- warning: set.Union₂_mono -> Set.unionᵢ₂_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {t : forall (i : ι), (κ i) -> (Set.{u1} α)}, (forall (i : ι) (j : κ i), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i j) (t i j)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => t i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u3} α)} {t : forall (i : ι), (κ i) -> (Set.{u3} α)}, (forall (i : ι) (j : κ i), HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (s i j) (t i j)) -> (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => t i j))))
Case conversion may be inaccurate. Consider using '#align set.Union₂_mono Set.unionᵢ₂_monoₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem unionᵢ₂_mono {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j ⊆ t i j) :
    (⋃ (i) (j), s i j) ⊆ ⋃ (i) (j), t i j :=
  @supᵢ₂_mono (Set α) _ _ _ s t h
#align set.Union₂_mono Set.unionᵢ₂_mono

/- warning: set.Inter_mono -> Set.interᵢ_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u1} α)}, (forall (i : ι), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i) (t i)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => t i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u2} α)}, (forall (i : ι), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (s i) (t i)) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.Inter_mono Set.interᵢ_monoₓ'. -/
theorem interᵢ_mono {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : (⋂ i, s i) ⊆ ⋂ i, t i :=
  @infᵢ_mono (Set α) _ _ s t h
#align set.Inter_mono Set.interᵢ_mono

/- warning: set.Inter₂_mono -> Set.interᵢ₂_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {t : forall (i : ι), (κ i) -> (Set.{u1} α)}, (forall (i : ι) (j : κ i), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i j) (t i j)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => t i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u3} α)} {t : forall (i : ι), (κ i) -> (Set.{u3} α)}, (forall (i : ι) (j : κ i), HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (s i j) (t i j)) -> (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => t i j))))
Case conversion may be inaccurate. Consider using '#align set.Inter₂_mono Set.interᵢ₂_monoₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem interᵢ₂_mono {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j ⊆ t i j) :
    (⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), t i j :=
  @infᵢ₂_mono (Set α) _ _ _ s t h
#align set.Inter₂_mono Set.interᵢ₂_mono

/- warning: set.Union_mono' -> Set.unionᵢ_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι₂ : Sort.{u3}} {s : ι -> (Set.{u1} α)} {t : ι₂ -> (Set.{u1} α)}, (forall (i : ι), Exists.{u3} ι₂ (fun (j : ι₂) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i) (t j))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u1, u3} α ι₂ (fun (i : ι₂) => t i)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u1}} {ι₂ : Sort.{u2}} {s : ι -> (Set.{u3} α)} {t : ι₂ -> (Set.{u3} α)}, (forall (i : ι), Exists.{u2} ι₂ (fun (j : ι₂) => HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (s i) (t j))) -> (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u3, u2} α ι₂ (fun (i : ι₂) => t i)))
Case conversion may be inaccurate. Consider using '#align set.Union_mono' Set.unionᵢ_mono'ₓ'. -/
theorem unionᵢ_mono' {s : ι → Set α} {t : ι₂ → Set α} (h : ∀ i, ∃ j, s i ⊆ t j) :
    (⋃ i, s i) ⊆ ⋃ i, t i :=
  @supᵢ_mono' (Set α) _ _ _ s t h
#align set.Union_mono' Set.unionᵢ_mono'

/- warning: set.Union₂_mono' -> Set.unionᵢ₂_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} {κ : ι -> Sort.{u4}} {κ' : ι' -> Sort.{u5}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {t : forall (i' : ι'), (κ' i') -> (Set.{u1} α)}, (forall (i : ι) (j : κ i), Exists.{u3} ι' (fun (i' : ι') => Exists.{u5} (κ' i') (fun (j' : κ' i') => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i j) (t i' j')))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u4} α (κ i) (fun (j : κ i) => s i j))) (Set.unionᵢ.{u1, u3} α ι' (fun (i' : ι') => Set.unionᵢ.{u1, u5} α (κ' i') (fun (j' : κ' i') => t i' j'))))
but is expected to have type
  forall {α : Type.{u5}} {ι : Sort.{u2}} {ι' : Sort.{u4}} {κ : ι -> Sort.{u1}} {κ' : ι' -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u5} α)} {t : forall (i' : ι'), (κ' i') -> (Set.{u5} α)}, (forall (i : ι) (j : κ i), Exists.{u4} ι' (fun (i' : ι') => Exists.{u3} (κ' i') (fun (j' : κ' i') => HasSubset.Subset.{u5} (Set.{u5} α) (Set.instHasSubsetSet.{u5} α) (s i j) (t i' j')))) -> (HasSubset.Subset.{u5} (Set.{u5} α) (Set.instHasSubsetSet.{u5} α) (Set.unionᵢ.{u5, u2} α ι (fun (i : ι) => Set.unionᵢ.{u5, u1} α (κ i) (fun (j : κ i) => s i j))) (Set.unionᵢ.{u5, u4} α ι' (fun (i' : ι') => Set.unionᵢ.{u5, u3} α (κ' i') (fun (j' : κ' i') => t i' j'))))
Case conversion may be inaccurate. Consider using '#align set.Union₂_mono' Set.unionᵢ₂_mono'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' j') -/
theorem unionᵢ₂_mono' {s : ∀ i, κ i → Set α} {t : ∀ i', κ' i' → Set α}
    (h : ∀ i j, ∃ i' j', s i j ⊆ t i' j') : (⋃ (i) (j), s i j) ⊆ ⋃ (i') (j'), t i' j' :=
  @supᵢ₂_mono' (Set α) _ _ _ _ _ s t h
#align set.Union₂_mono' Set.unionᵢ₂_mono'

/- warning: set.Inter_mono' -> Set.interᵢ_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} {s : ι -> (Set.{u1} α)} {t : ι' -> (Set.{u1} α)}, (forall (j : ι'), Exists.{u2} ι (fun (i : ι) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i) (t j))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u1, u3} α ι' (fun (j : ι') => t j)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} {s : ι -> (Set.{u3} α)} {t : ι' -> (Set.{u3} α)}, (forall (j : ι'), Exists.{u2} ι (fun (i : ι) => HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (s i) (t j))) -> (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u3, u1} α ι' (fun (j : ι') => t j)))
Case conversion may be inaccurate. Consider using '#align set.Inter_mono' Set.interᵢ_mono'ₓ'. -/
theorem interᵢ_mono' {s : ι → Set α} {t : ι' → Set α} (h : ∀ j, ∃ i, s i ⊆ t j) :
    (⋂ i, s i) ⊆ ⋂ j, t j :=
  Set.subset_interᵢ fun j =>
    let ⟨i, hi⟩ := h j
    interᵢ_subset_of_subset i hi
#align set.Inter_mono' Set.interᵢ_mono'

/- warning: set.Inter₂_mono' -> Set.interᵢ₂_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} {κ : ι -> Sort.{u4}} {κ' : ι' -> Sort.{u5}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {t : forall (i' : ι'), (κ' i') -> (Set.{u1} α)}, (forall (i' : ι') (j' : κ' i'), Exists.{u2} ι (fun (i : ι) => Exists.{u4} (κ i) (fun (j : κ i) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (s i j) (t i' j')))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u4} α (κ i) (fun (j : κ i) => s i j))) (Set.interᵢ.{u1, u3} α ι' (fun (i' : ι') => Set.interᵢ.{u1, u5} α (κ' i') (fun (j' : κ' i') => t i' j'))))
but is expected to have type
  forall {α : Type.{u5}} {ι : Sort.{u4}} {ι' : Sort.{u2}} {κ : ι -> Sort.{u3}} {κ' : ι' -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u5} α)} {t : forall (i' : ι'), (κ' i') -> (Set.{u5} α)}, (forall (i' : ι') (j' : κ' i'), Exists.{u4} ι (fun (i : ι) => Exists.{u3} (κ i) (fun (j : κ i) => HasSubset.Subset.{u5} (Set.{u5} α) (Set.instHasSubsetSet.{u5} α) (s i j) (t i' j')))) -> (HasSubset.Subset.{u5} (Set.{u5} α) (Set.instHasSubsetSet.{u5} α) (Set.interᵢ.{u5, u4} α ι (fun (i : ι) => Set.interᵢ.{u5, u3} α (κ i) (fun (j : κ i) => s i j))) (Set.interᵢ.{u5, u2} α ι' (fun (i' : ι') => Set.interᵢ.{u5, u1} α (κ' i') (fun (j' : κ' i') => t i' j'))))
Case conversion may be inaccurate. Consider using '#align set.Inter₂_mono' Set.interᵢ₂_mono'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' j') -/
theorem interᵢ₂_mono' {s : ∀ i, κ i → Set α} {t : ∀ i', κ' i' → Set α}
    (h : ∀ i' j', ∃ i j, s i j ⊆ t i' j') : (⋂ (i) (j), s i j) ⊆ ⋂ (i') (j'), t i' j' :=
  subset_interᵢ₂_iff.2 fun i' j' =>
    let ⟨i, j, hst⟩ := h i' j'
    (interᵢ₂_subset _ _).trans hst
#align set.Inter₂_mono' Set.interᵢ₂_mono'

/- warning: set.Union₂_subset_Union -> Set.unionᵢ₂_subset_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (κ : ι -> Sort.{u3}) (s : ι -> (Set.{u1} α)), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (κ : ι -> Sort.{u3}) (s : ι -> (Set.{u2} α)), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, u3} α (κ i) (fun (j : κ i) => s i))) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i))
Case conversion may be inaccurate. Consider using '#align set.Union₂_subset_Union Set.unionᵢ₂_subset_unionᵢₓ'. -/
theorem unionᵢ₂_subset_unionᵢ (κ : ι → Sort _) (s : ι → Set α) :
    (⋃ (i) (j : κ i), s i) ⊆ ⋃ i, s i :=
  Union_mono fun i => Union_subset fun h => Subset.rfl
#align set.Union₂_subset_Union Set.unionᵢ₂_subset_unionᵢ

/- warning: set.Inter_subset_Inter₂ -> Set.interᵢ_subset_interᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (κ : ι -> Sort.{u3}) (s : ι -> (Set.{u1} α)), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (κ : ι -> Sort.{u3}) (s : ι -> (Set.{u2} α)), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Set.interᵢ.{u2, u3} α (κ i) (fun (j : κ i) => s i)))
Case conversion may be inaccurate. Consider using '#align set.Inter_subset_Inter₂ Set.interᵢ_subset_interᵢ₂ₓ'. -/
theorem interᵢ_subset_interᵢ₂ (κ : ι → Sort _) (s : ι → Set α) :
    (⋂ i, s i) ⊆ ⋂ (i) (j : κ i), s i :=
  Inter_mono fun i => subset_Inter fun h => Subset.rfl
#align set.Inter_subset_Inter₂ Set.interᵢ_subset_interᵢ₂

/- warning: set.Union_set_of -> Set.unionᵢ_setOf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (P : ι -> α -> Prop), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => setOf.{u1} α (fun (x : α) => P i x))) (setOf.{u1} α (fun (x : α) => Exists.{u2} ι (fun (i : ι) => P i x)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (P : ι -> α -> Prop), Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => setOf.{u2} α (fun (x : α) => P i x))) (setOf.{u2} α (fun (x : α) => Exists.{u1} ι (fun (i : ι) => P i x)))
Case conversion may be inaccurate. Consider using '#align set.Union_set_of Set.unionᵢ_setOfₓ'. -/
theorem unionᵢ_setOf (P : ι → α → Prop) : (⋃ i, { x : α | P i x }) = { x : α | ∃ i, P i x } :=
  by
  ext
  exact mem_Union
#align set.Union_set_of Set.unionᵢ_setOf

/- warning: set.Inter_set_of -> Set.interᵢ_setOf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (P : ι -> α -> Prop), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => setOf.{u1} α (fun (x : α) => P i x))) (setOf.{u1} α (fun (x : α) => forall (i : ι), P i x))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (P : ι -> α -> Prop), Eq.{succ u2} (Set.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => setOf.{u2} α (fun (x : α) => P i x))) (setOf.{u2} α (fun (x : α) => forall (i : ι), P i x))
Case conversion may be inaccurate. Consider using '#align set.Inter_set_of Set.interᵢ_setOfₓ'. -/
theorem interᵢ_setOf (P : ι → α → Prop) : (⋂ i, { x : α | P i x }) = { x : α | ∀ i, P i x } :=
  by
  ext
  exact mem_Inter
#align set.Inter_set_of Set.interᵢ_setOf

/- warning: set.Union_congr_of_surjective -> Set.unionᵢ_congr_of_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι₂ : Sort.{u3}} {f : ι -> (Set.{u1} α)} {g : ι₂ -> (Set.{u1} α)} (h : ι -> ι₂), (Function.Surjective.{u2, u3} ι ι₂ h) -> (forall (x : ι), Eq.{succ u1} (Set.{u1} α) (g (h x)) (f x)) -> (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (x : ι) => f x)) (Set.unionᵢ.{u1, u3} α ι₂ (fun (y : ι₂) => g y)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι₂ : Sort.{u1}} {f : ι -> (Set.{u3} α)} {g : ι₂ -> (Set.{u3} α)} (h : ι -> ι₂), (Function.Surjective.{u2, u1} ι ι₂ h) -> (forall (x : ι), Eq.{succ u3} (Set.{u3} α) (g (h x)) (f x)) -> (Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, u2} α ι (fun (x : ι) => f x)) (Set.unionᵢ.{u3, u1} α ι₂ (fun (y : ι₂) => g y)))
Case conversion may be inaccurate. Consider using '#align set.Union_congr_of_surjective Set.unionᵢ_congr_of_surjectiveₓ'. -/
theorem unionᵢ_congr_of_surjective {f : ι → Set α} {g : ι₂ → Set α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⋃ x, f x) = ⋃ y, g y :=
  h1.supr_congr h h2
#align set.Union_congr_of_surjective Set.unionᵢ_congr_of_surjective

/- warning: set.Inter_congr_of_surjective -> Set.interᵢ_congr_of_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι₂ : Sort.{u3}} {f : ι -> (Set.{u1} α)} {g : ι₂ -> (Set.{u1} α)} (h : ι -> ι₂), (Function.Surjective.{u2, u3} ι ι₂ h) -> (forall (x : ι), Eq.{succ u1} (Set.{u1} α) (g (h x)) (f x)) -> (Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (x : ι) => f x)) (Set.interᵢ.{u1, u3} α ι₂ (fun (y : ι₂) => g y)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι₂ : Sort.{u1}} {f : ι -> (Set.{u3} α)} {g : ι₂ -> (Set.{u3} α)} (h : ι -> ι₂), (Function.Surjective.{u2, u1} ι ι₂ h) -> (forall (x : ι), Eq.{succ u3} (Set.{u3} α) (g (h x)) (f x)) -> (Eq.{succ u3} (Set.{u3} α) (Set.interᵢ.{u3, u2} α ι (fun (x : ι) => f x)) (Set.interᵢ.{u3, u1} α ι₂ (fun (y : ι₂) => g y)))
Case conversion may be inaccurate. Consider using '#align set.Inter_congr_of_surjective Set.interᵢ_congr_of_surjectiveₓ'. -/
theorem interᵢ_congr_of_surjective {f : ι → Set α} {g : ι₂ → Set α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⋂ x, f x) = ⋂ y, g y :=
  h1.infi_congr h h2
#align set.Inter_congr_of_surjective Set.interᵢ_congr_of_surjective

/- warning: set.Union_congr -> Set.unionᵢ_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u1} α)}, (forall (i : ι), Eq.{succ u1} (Set.{u1} α) (s i) (t i)) -> (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => t i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u2} α)}, (forall (i : ι), Eq.{succ u2} (Set.{u2} α) (s i) (t i)) -> (Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.Union_congr Set.unionᵢ_congrₓ'. -/
theorem unionᵢ_congr {s t : ι → Set α} (h : ∀ i, s i = t i) : (⋃ i, s i) = ⋃ i, t i :=
  supᵢ_congr h
#align set.Union_congr Set.unionᵢ_congr

/- warning: set.Inter_congr -> Set.interᵢ_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u1} α)}, (forall (i : ι), Eq.{succ u1} (Set.{u1} α) (s i) (t i)) -> (Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => t i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u2} α)}, (forall (i : ι), Eq.{succ u2} (Set.{u2} α) (s i) (t i)) -> (Eq.{succ u2} (Set.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.Inter_congr Set.interᵢ_congrₓ'. -/
theorem interᵢ_congr {s t : ι → Set α} (h : ∀ i, s i = t i) : (⋂ i, s i) = ⋂ i, t i :=
  infᵢ_congr h
#align set.Inter_congr Set.interᵢ_congr

/- warning: set.Union₂_congr -> Set.unionᵢ₂_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {t : forall (i : ι), (κ i) -> (Set.{u1} α)}, (forall (i : ι) (j : κ i), Eq.{succ u1} (Set.{u1} α) (s i j) (t i j)) -> (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => t i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u3} α)} {t : forall (i : ι), (κ i) -> (Set.{u3} α)}, (forall (i : ι) (j : κ i), Eq.{succ u3} (Set.{u3} α) (s i j) (t i j)) -> (Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => t i j))))
Case conversion may be inaccurate. Consider using '#align set.Union₂_congr Set.unionᵢ₂_congrₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem unionᵢ₂_congr {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j = t i j) :
    (⋃ (i) (j), s i j) = ⋃ (i) (j), t i j :=
  Union_congr fun i => Union_congr <| h i
#align set.Union₂_congr Set.unionᵢ₂_congr

/- warning: set.Inter₂_congr -> Set.interᵢ₂_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {t : forall (i : ι), (κ i) -> (Set.{u1} α)}, (forall (i : ι) (j : κ i), Eq.{succ u1} (Set.{u1} α) (s i j) (t i j)) -> (Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => t i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u3} α)} {t : forall (i : ι), (κ i) -> (Set.{u3} α)}, (forall (i : ι) (j : κ i), Eq.{succ u3} (Set.{u3} α) (s i j) (t i j)) -> (Eq.{succ u3} (Set.{u3} α) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => t i j))))
Case conversion may be inaccurate. Consider using '#align set.Inter₂_congr Set.interᵢ₂_congrₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem interᵢ₂_congr {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j = t i j) :
    (⋂ (i) (j), s i j) = ⋂ (i) (j), t i j :=
  Inter_congr fun i => Inter_congr <| h i
#align set.Inter₂_congr Set.interᵢ₂_congr

section Nonempty

variable [Nonempty ι] {f : ι → Set α} {s : Set α}

/- warning: set.Union_const -> Set.unionᵢ_const is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] (s : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => s)) s
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] (s : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => s)) s
Case conversion may be inaccurate. Consider using '#align set.Union_const Set.unionᵢ_constₓ'. -/
theorem unionᵢ_const (s : Set β) : (⋃ i : ι, s) = s :=
  supᵢ_const
#align set.Union_const Set.unionᵢ_const

/- warning: set.Inter_const -> Set.interᵢ_const is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] (s : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => s)) s
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] (s : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => s)) s
Case conversion may be inaccurate. Consider using '#align set.Inter_const Set.interᵢ_constₓ'. -/
theorem interᵢ_const (s : Set β) : (⋂ i : ι, s) = s :=
  infᵢ_const
#align set.Inter_const Set.interᵢ_const

/- warning: set.Union_eq_const -> Set.unionᵢ_eq_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] {f : ι -> (Set.{u1} α)} {s : Set.{u1} α}, (forall (i : ι), Eq.{succ u1} (Set.{u1} α) (f i) s) -> (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => f i)) s)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {f : ι -> (Set.{u2} α)} {s : Set.{u2} α}, (forall (i : ι), Eq.{succ u2} (Set.{u2} α) (f i) s) -> (Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => f i)) s)
Case conversion may be inaccurate. Consider using '#align set.Union_eq_const Set.unionᵢ_eq_constₓ'. -/
theorem unionᵢ_eq_const (hf : ∀ i, f i = s) : (⋃ i, f i) = s :=
  (unionᵢ_congr hf).trans <| unionᵢ_const _
#align set.Union_eq_const Set.unionᵢ_eq_const

/- warning: set.Inter_eq_const -> Set.interᵢ_eq_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] {f : ι -> (Set.{u1} α)} {s : Set.{u1} α}, (forall (i : ι), Eq.{succ u1} (Set.{u1} α) (f i) s) -> (Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => f i)) s)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {f : ι -> (Set.{u2} α)} {s : Set.{u2} α}, (forall (i : ι), Eq.{succ u2} (Set.{u2} α) (f i) s) -> (Eq.{succ u2} (Set.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => f i)) s)
Case conversion may be inaccurate. Consider using '#align set.Inter_eq_const Set.interᵢ_eq_constₓ'. -/
theorem interᵢ_eq_const (hf : ∀ i, f i = s) : (⋂ i, f i) = s :=
  (interᵢ_congr hf).trans <| interᵢ_const _
#align set.Inter_eq_const Set.interᵢ_eq_const

end Nonempty

/- warning: set.compl_Union -> Set.compl_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.booleanAlgebra.{u1} β)) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => s i))) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.booleanAlgebra.{u1} β)) (s i)))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => s i))) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (s i)))
Case conversion may be inaccurate. Consider using '#align set.compl_Union Set.compl_unionᵢₓ'. -/
@[simp]
theorem compl_unionᵢ (s : ι → Set β) : (⋃ i, s i)ᶜ = ⋂ i, s iᶜ :=
  compl_supᵢ
#align set.compl_Union Set.compl_unionᵢ

/- warning: set.compl_Union₂ -> Set.compl_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} (s : forall (i : ι), (κ i) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j)))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (s i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} (s : forall (i : ι), (κ i) -> (Set.{u3} α)), Eq.{succ u3} (Set.{u3} α) (HasCompl.compl.{u3} (Set.{u3} α) (BooleanAlgebra.toHasCompl.{u3} (Set.{u3} α) (Set.instBooleanAlgebraSet.{u3} α)) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j)))) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => HasCompl.compl.{u3} (Set.{u3} α) (BooleanAlgebra.toHasCompl.{u3} (Set.{u3} α) (Set.instBooleanAlgebraSet.{u3} α)) (s i j))))
Case conversion may be inaccurate. Consider using '#align set.compl_Union₂ Set.compl_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem compl_unionᵢ₂ (s : ∀ i, κ i → Set α) : (⋃ (i) (j), s i j)ᶜ = ⋂ (i) (j), s i jᶜ := by
  simp_rw [compl_Union]
#align set.compl_Union₂ Set.compl_unionᵢ₂

/- warning: set.compl_Inter -> Set.compl_interᵢ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.booleanAlgebra.{u1} β)) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => s i))) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.booleanAlgebra.{u1} β)) (s i)))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => s i))) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (s i)))
Case conversion may be inaccurate. Consider using '#align set.compl_Inter Set.compl_interᵢₓ'. -/
@[simp]
theorem compl_interᵢ (s : ι → Set β) : (⋂ i, s i)ᶜ = ⋃ i, s iᶜ :=
  compl_infᵢ
#align set.compl_Inter Set.compl_interᵢ

/- warning: set.compl_Inter₂ -> Set.compl_interᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} (s : forall (i : ι), (κ i) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j)))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (s i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} (s : forall (i : ι), (κ i) -> (Set.{u3} α)), Eq.{succ u3} (Set.{u3} α) (HasCompl.compl.{u3} (Set.{u3} α) (BooleanAlgebra.toHasCompl.{u3} (Set.{u3} α) (Set.instBooleanAlgebraSet.{u3} α)) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j)))) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => HasCompl.compl.{u3} (Set.{u3} α) (BooleanAlgebra.toHasCompl.{u3} (Set.{u3} α) (Set.instBooleanAlgebraSet.{u3} α)) (s i j))))
Case conversion may be inaccurate. Consider using '#align set.compl_Inter₂ Set.compl_interᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem compl_interᵢ₂ (s : ∀ i, κ i → Set α) : (⋂ (i) (j), s i j)ᶜ = ⋃ (i) (j), s i jᶜ := by
  simp_rw [compl_Inter]
#align set.compl_Inter₂ Set.compl_interᵢ₂

/- warning: set.Union_eq_compl_Inter_compl -> Set.unionᵢ_eq_compl_interᵢ_compl is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => s i)) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.booleanAlgebra.{u1} β)) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.booleanAlgebra.{u1} β)) (s i))))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => s i)) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (s i))))
Case conversion may be inaccurate. Consider using '#align set.Union_eq_compl_Inter_compl Set.unionᵢ_eq_compl_interᵢ_complₓ'. -/
-- classical -- complete_boolean_algebra
theorem unionᵢ_eq_compl_interᵢ_compl (s : ι → Set β) : (⋃ i, s i) = (⋂ i, s iᶜ)ᶜ := by
  simp only [compl_Inter, compl_compl]
#align set.Union_eq_compl_Inter_compl Set.unionᵢ_eq_compl_interᵢ_compl

/- warning: set.Inter_eq_compl_Union_compl -> Set.interᵢ_eq_compl_unionᵢ_compl is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => s i)) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.booleanAlgebra.{u1} β)) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.booleanAlgebra.{u1} β)) (s i))))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => s i)) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (s i))))
Case conversion may be inaccurate. Consider using '#align set.Inter_eq_compl_Union_compl Set.interᵢ_eq_compl_unionᵢ_complₓ'. -/
-- classical -- complete_boolean_algebra
theorem interᵢ_eq_compl_unionᵢ_compl (s : ι → Set β) : (⋂ i, s i) = (⋃ i, s iᶜ)ᶜ := by
  simp only [compl_Union, compl_compl]
#align set.Inter_eq_compl_Union_compl Set.interᵢ_eq_compl_unionᵢ_compl

/- warning: set.inter_Union -> Set.inter_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (s : Set.{u1} β) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.hasInter.{u1} β) s (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => t i))) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => Inter.inter.{u1} (Set.{u1} β) (Set.hasInter.{u1} β) s (t i)))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (s : Set.{u2} β) (t : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) s (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => t i))) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) s (t i)))
Case conversion may be inaccurate. Consider using '#align set.inter_Union Set.inter_unionᵢₓ'. -/
theorem inter_unionᵢ (s : Set β) (t : ι → Set β) : (s ∩ ⋃ i, t i) = ⋃ i, s ∩ t i :=
  inf_supᵢ_eq _ _
#align set.inter_Union Set.inter_unionᵢ

/- warning: set.Union_inter -> Set.unionᵢ_inter is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (s : Set.{u1} β) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.hasInter.{u1} β) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => t i)) s) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => Inter.inter.{u1} (Set.{u1} β) (Set.hasInter.{u1} β) (t i) s))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (s : Set.{u2} β) (t : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => t i)) s) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (t i) s))
Case conversion may be inaccurate. Consider using '#align set.Union_inter Set.unionᵢ_interₓ'. -/
theorem unionᵢ_inter (s : Set β) (t : ι → Set β) : (⋃ i, t i) ∩ s = ⋃ i, t i ∩ s :=
  supᵢ_inf_eq _ _
#align set.Union_inter Set.unionᵢ_inter

/- warning: set.Union_union_distrib -> Set.unionᵢ_union_distrib is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} β)) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => Union.union.{u1} (Set.{u1} β) (Set.hasUnion.{u1} β) (s i) (t i))) (Union.union.{u1} (Set.{u1} β) (Set.hasUnion.{u1} β) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => s i)) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => t i)))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} β)) (t : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) (s i) (t i))) (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => s i)) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.Union_union_distrib Set.unionᵢ_union_distribₓ'. -/
theorem unionᵢ_union_distrib (s : ι → Set β) (t : ι → Set β) :
    (⋃ i, s i ∪ t i) = (⋃ i, s i) ∪ ⋃ i, t i :=
  supᵢ_sup_eq
#align set.Union_union_distrib Set.unionᵢ_union_distrib

/- warning: set.Inter_inter_distrib -> Set.interᵢ_inter_distrib is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} β)) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => Inter.inter.{u1} (Set.{u1} β) (Set.hasInter.{u1} β) (s i) (t i))) (Inter.inter.{u1} (Set.{u1} β) (Set.hasInter.{u1} β) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => s i)) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => t i)))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} β)) (t : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (s i) (t i))) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => s i)) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.Inter_inter_distrib Set.interᵢ_inter_distribₓ'. -/
theorem interᵢ_inter_distrib (s : ι → Set β) (t : ι → Set β) :
    (⋂ i, s i ∩ t i) = (⋂ i, s i) ∩ ⋂ i, t i :=
  infᵢ_inf_eq
#align set.Inter_inter_distrib Set.interᵢ_inter_distrib

/- warning: set.union_Union -> Set.union_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] (s : Set.{u1} β) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Union.union.{u1} (Set.{u1} β) (Set.hasUnion.{u1} β) s (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => t i))) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => Union.union.{u1} (Set.{u1} β) (Set.hasUnion.{u1} β) s (t i)))
but is expected to have type
  forall {β : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] (s : Set.{u1} β) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) s (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => t i))) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) s (t i)))
Case conversion may be inaccurate. Consider using '#align set.union_Union Set.union_unionᵢₓ'. -/
theorem union_unionᵢ [Nonempty ι] (s : Set β) (t : ι → Set β) : (s ∪ ⋃ i, t i) = ⋃ i, s ∪ t i :=
  sup_supᵢ
#align set.union_Union Set.union_unionᵢ

/- warning: set.Union_union -> Set.unionᵢ_union is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] (s : Set.{u1} β) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Union.union.{u1} (Set.{u1} β) (Set.hasUnion.{u1} β) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => t i)) s) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => Union.union.{u1} (Set.{u1} β) (Set.hasUnion.{u1} β) (t i) s))
but is expected to have type
  forall {β : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] (s : Set.{u1} β) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => t i)) s) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) (t i) s))
Case conversion may be inaccurate. Consider using '#align set.Union_union Set.unionᵢ_unionₓ'. -/
theorem unionᵢ_union [Nonempty ι] (s : Set β) (t : ι → Set β) : (⋃ i, t i) ∪ s = ⋃ i, t i ∪ s :=
  supᵢ_sup
#align set.Union_union Set.unionᵢ_union

/- warning: set.inter_Inter -> Set.inter_interᵢ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] (s : Set.{u1} β) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.hasInter.{u1} β) s (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => t i))) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => Inter.inter.{u1} (Set.{u1} β) (Set.hasInter.{u1} β) s (t i)))
but is expected to have type
  forall {β : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] (s : Set.{u1} β) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) s (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => t i))) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) s (t i)))
Case conversion may be inaccurate. Consider using '#align set.inter_Inter Set.inter_interᵢₓ'. -/
theorem inter_interᵢ [Nonempty ι] (s : Set β) (t : ι → Set β) : (s ∩ ⋂ i, t i) = ⋂ i, s ∩ t i :=
  inf_infᵢ
#align set.inter_Inter Set.inter_interᵢ

/- warning: set.Inter_inter -> Set.interᵢ_inter is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] (s : Set.{u1} β) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.hasInter.{u1} β) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => t i)) s) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => Inter.inter.{u1} (Set.{u1} β) (Set.hasInter.{u1} β) (t i) s))
but is expected to have type
  forall {β : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] (s : Set.{u1} β) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => t i)) s) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (t i) s))
Case conversion may be inaccurate. Consider using '#align set.Inter_inter Set.interᵢ_interₓ'. -/
theorem interᵢ_inter [Nonempty ι] (s : Set β) (t : ι → Set β) : (⋂ i, t i) ∩ s = ⋂ i, t i ∩ s :=
  infᵢ_inf
#align set.Inter_inter Set.interᵢ_inter

/- warning: set.union_Inter -> Set.union_interᵢ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (s : Set.{u1} β) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Union.union.{u1} (Set.{u1} β) (Set.hasUnion.{u1} β) s (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => t i))) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => Union.union.{u1} (Set.{u1} β) (Set.hasUnion.{u1} β) s (t i)))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (s : Set.{u2} β) (t : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => t i))) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s (t i)))
Case conversion may be inaccurate. Consider using '#align set.union_Inter Set.union_interᵢₓ'. -/
-- classical
theorem union_interᵢ (s : Set β) (t : ι → Set β) : (s ∪ ⋂ i, t i) = ⋂ i, s ∪ t i :=
  sup_infᵢ_eq _ _
#align set.union_Inter Set.union_interᵢ

/- warning: set.Inter_union -> Set.interᵢ_union is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} β)) (t : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Union.union.{u1} (Set.{u1} β) (Set.hasUnion.{u1} β) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => s i)) t) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => Union.union.{u1} (Set.{u1} β) (Set.hasUnion.{u1} β) (s i) t))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} β)) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => s i)) t) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) (s i) t))
Case conversion may be inaccurate. Consider using '#align set.Inter_union Set.interᵢ_unionₓ'. -/
theorem interᵢ_union (s : ι → Set β) (t : Set β) : (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
  infᵢ_sup_eq _ _
#align set.Inter_union Set.interᵢ_union

/- warning: set.Union_diff -> Set.unionᵢ_diff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (s : Set.{u1} β) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (SDiff.sdiff.{u1} (Set.{u1} β) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} β) (Set.booleanAlgebra.{u1} β)) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => t i)) s) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => SDiff.sdiff.{u1} (Set.{u1} β) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} β) (Set.booleanAlgebra.{u1} β)) (t i) s))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (s : Set.{u2} β) (t : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (SDiff.sdiff.{u2} (Set.{u2} β) (Set.instSDiffSet.{u2} β) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => t i)) s) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => SDiff.sdiff.{u2} (Set.{u2} β) (Set.instSDiffSet.{u2} β) (t i) s))
Case conversion may be inaccurate. Consider using '#align set.Union_diff Set.unionᵢ_diffₓ'. -/
theorem unionᵢ_diff (s : Set β) (t : ι → Set β) : (⋃ i, t i) \ s = ⋃ i, t i \ s :=
  unionᵢ_inter _ _
#align set.Union_diff Set.unionᵢ_diff

/- warning: set.diff_Union -> Set.diff_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] (s : Set.{u1} β) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (SDiff.sdiff.{u1} (Set.{u1} β) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} β) (Set.booleanAlgebra.{u1} β)) s (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => t i))) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => SDiff.sdiff.{u1} (Set.{u1} β) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} β) (Set.booleanAlgebra.{u1} β)) s (t i)))
but is expected to have type
  forall {β : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] (s : Set.{u1} β) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (SDiff.sdiff.{u1} (Set.{u1} β) (Set.instSDiffSet.{u1} β) s (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => t i))) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => SDiff.sdiff.{u1} (Set.{u1} β) (Set.instSDiffSet.{u1} β) s (t i)))
Case conversion may be inaccurate. Consider using '#align set.diff_Union Set.diff_unionᵢₓ'. -/
theorem diff_unionᵢ [Nonempty ι] (s : Set β) (t : ι → Set β) : (s \ ⋃ i, t i) = ⋂ i, s \ t i := by
  rw [diff_eq, compl_Union, inter_Inter] <;> rfl
#align set.diff_Union Set.diff_unionᵢ

/- warning: set.diff_Inter -> Set.diff_interᵢ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (s : Set.{u1} β) (t : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (SDiff.sdiff.{u1} (Set.{u1} β) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} β) (Set.booleanAlgebra.{u1} β)) s (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => t i))) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => SDiff.sdiff.{u1} (Set.{u1} β) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} β) (Set.booleanAlgebra.{u1} β)) s (t i)))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (s : Set.{u2} β) (t : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (SDiff.sdiff.{u2} (Set.{u2} β) (Set.instSDiffSet.{u2} β) s (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => t i))) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => SDiff.sdiff.{u2} (Set.{u2} β) (Set.instSDiffSet.{u2} β) s (t i)))
Case conversion may be inaccurate. Consider using '#align set.diff_Inter Set.diff_interᵢₓ'. -/
theorem diff_interᵢ (s : Set β) (t : ι → Set β) : (s \ ⋂ i, t i) = ⋃ i, s \ t i := by
  rw [diff_eq, compl_Inter, inter_Union] <;> rfl
#align set.diff_Inter Set.diff_interᵢ

/- warning: set.directed_on_Union -> Set.directed_on_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {r : α -> α -> Prop} {f : ι -> (Set.{u1} α)}, (Directed.{u1, u2} (Set.{u1} α) ι (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α)) f) -> (forall (x : ι), DirectedOn.{u1} α r (f x)) -> (DirectedOn.{u1} α r (Set.unionᵢ.{u1, u2} α ι (fun (x : ι) => f x)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {r : α -> α -> Prop} {f : ι -> (Set.{u2} α)}, (Directed.{u2, u1} (Set.{u2} α) ι (fun (x._@.Mathlib.Data.Set.Lattice._hyg.9356 : Set.{u2} α) (x._@.Mathlib.Data.Set.Lattice._hyg.9358 : Set.{u2} α) => HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) x._@.Mathlib.Data.Set.Lattice._hyg.9356 x._@.Mathlib.Data.Set.Lattice._hyg.9358) f) -> (forall (x : ι), DirectedOn.{u2} α r (f x)) -> (DirectedOn.{u2} α r (Set.unionᵢ.{u2, u1} α ι (fun (x : ι) => f x)))
Case conversion may be inaccurate. Consider using '#align set.directed_on_Union Set.directed_on_unionᵢₓ'. -/
theorem directed_on_unionᵢ {r} {f : ι → Set α} (hd : Directed (· ⊆ ·) f)
    (h : ∀ x, DirectedOn r (f x)) : DirectedOn r (⋃ x, f x) := by
  simp only [DirectedOn, exists_prop, mem_Union, exists_imp] <;>
    exact fun a₁ b₁ fb₁ a₂ b₂ fb₂ =>
      let ⟨z, zb₁, zb₂⟩ := hd b₁ b₂
      let ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂)
      ⟨x, ⟨z, xf⟩, xa₁, xa₂⟩
#align set.directed_on_Union Set.directed_on_unionᵢ

/- warning: set.Union_inter_subset -> Set.unionᵢ_inter_subset is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u2} α)}, HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => Inter.inter.{u2} (Set.{u2} α) (Set.hasInter.{u2} α) (s i) (t i))) (Inter.inter.{u2} (Set.{u2} α) (Set.hasInter.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => t i)))
but is expected to have type
  forall {ι : Sort.{u2}} {α : Type.{u1}} {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u1} α)}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (s i) (t i))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.Union_inter_subset Set.unionᵢ_inter_subsetₓ'. -/
theorem unionᵢ_inter_subset {ι α} {s t : ι → Set α} : (⋃ i, s i ∩ t i) ⊆ (⋃ i, s i) ∩ ⋃ i, t i :=
  le_supᵢ_inf_supᵢ s t
#align set.Union_inter_subset Set.unionᵢ_inter_subset

/- warning: set.Union_inter_of_monotone -> Set.unionᵢ_inter_of_monotone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} ι] [_inst_2 : IsDirected.{u1} ι (LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_1))] {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u2} α)}, (Monotone.{u1, u2} ι (Set.{u2} α) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) s) -> (Monotone.{u1, u2} ι (Set.{u2} α) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) t) -> (Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => Inter.inter.{u2} (Set.{u2} α) (Set.hasInter.{u2} α) (s i) (t i))) (Inter.inter.{u2} (Set.{u2} α) (Set.hasInter.{u2} α) (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => t i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : IsDirected.{u2} ι (fun (x._@.Mathlib.Data.Set.Lattice._hyg.9630 : ι) (x._@.Mathlib.Data.Set.Lattice._hyg.9632 : ι) => LE.le.{u2} ι (Preorder.toLE.{u2} ι _inst_1) x._@.Mathlib.Data.Set.Lattice._hyg.9630 x._@.Mathlib.Data.Set.Lattice._hyg.9632)] {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u1} α)}, (Monotone.{u2, u1} ι (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) s) -> (Monotone.{u2, u1} ι (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) t) -> (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (s i) (t i))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => t i))))
Case conversion may be inaccurate. Consider using '#align set.Union_inter_of_monotone Set.unionᵢ_inter_of_monotoneₓ'. -/
theorem unionᵢ_inter_of_monotone {ι α} [Preorder ι] [IsDirected ι (· ≤ ·)] {s t : ι → Set α}
    (hs : Monotone s) (ht : Monotone t) : (⋃ i, s i ∩ t i) = (⋃ i, s i) ∩ ⋃ i, t i :=
  supᵢ_inf_of_monotone hs ht
#align set.Union_inter_of_monotone Set.unionᵢ_inter_of_monotone

/- warning: set.Union_inter_of_antitone -> Set.unionᵢ_inter_of_antitone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} ι] [_inst_2 : IsDirected.{u1} ι (Function.swap.{succ u1, succ u1, 1} ι ι (fun (ᾰ : ι) (ᾰ : ι) => Prop) (LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_1)))] {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u2} α)}, (Antitone.{u1, u2} ι (Set.{u2} α) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) s) -> (Antitone.{u1, u2} ι (Set.{u2} α) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) t) -> (Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => Inter.inter.{u2} (Set.{u2} α) (Set.hasInter.{u2} α) (s i) (t i))) (Inter.inter.{u2} (Set.{u2} α) (Set.hasInter.{u2} α) (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => t i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : IsDirected.{u2} ι (Function.swap.{succ u2, succ u2, 1} ι ι (fun (ᾰ : ι) (ᾰ : ι) => Prop) (fun (x._@.Mathlib.Data.Set.Lattice._hyg.9760 : ι) (x._@.Mathlib.Data.Set.Lattice._hyg.9762 : ι) => LE.le.{u2} ι (Preorder.toLE.{u2} ι _inst_1) x._@.Mathlib.Data.Set.Lattice._hyg.9760 x._@.Mathlib.Data.Set.Lattice._hyg.9762))] {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u1} α)}, (Antitone.{u2, u1} ι (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) s) -> (Antitone.{u2, u1} ι (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) t) -> (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (s i) (t i))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => t i))))
Case conversion may be inaccurate. Consider using '#align set.Union_inter_of_antitone Set.unionᵢ_inter_of_antitoneₓ'. -/
theorem unionᵢ_inter_of_antitone {ι α} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {s t : ι → Set α}
    (hs : Antitone s) (ht : Antitone t) : (⋃ i, s i ∩ t i) = (⋃ i, s i) ∩ ⋃ i, t i :=
  supᵢ_inf_of_antitone hs ht
#align set.Union_inter_of_antitone Set.unionᵢ_inter_of_antitone

/- warning: set.Inter_union_of_monotone -> Set.interᵢ_union_of_monotone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} ι] [_inst_2 : IsDirected.{u1} ι (Function.swap.{succ u1, succ u1, 1} ι ι (fun (ᾰ : ι) (ᾰ : ι) => Prop) (LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_1)))] {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u2} α)}, (Monotone.{u1, u2} ι (Set.{u2} α) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) s) -> (Monotone.{u1, u2} ι (Set.{u2} α) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) t) -> (Eq.{succ u2} (Set.{u2} α) (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => Union.union.{u2} (Set.{u2} α) (Set.hasUnion.{u2} α) (s i) (t i))) (Union.union.{u2} (Set.{u2} α) (Set.hasUnion.{u2} α) (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => t i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : IsDirected.{u2} ι (Function.swap.{succ u2, succ u2, 1} ι ι (fun (ᾰ : ι) (ᾰ : ι) => Prop) (fun (x._@.Mathlib.Data.Set.Lattice._hyg.9890 : ι) (x._@.Mathlib.Data.Set.Lattice._hyg.9892 : ι) => LE.le.{u2} ι (Preorder.toLE.{u2} ι _inst_1) x._@.Mathlib.Data.Set.Lattice._hyg.9890 x._@.Mathlib.Data.Set.Lattice._hyg.9892))] {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u1} α)}, (Monotone.{u2, u1} ι (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) s) -> (Monotone.{u2, u1} ι (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) t) -> (Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (s i) (t i))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => t i))))
Case conversion may be inaccurate. Consider using '#align set.Inter_union_of_monotone Set.interᵢ_union_of_monotoneₓ'. -/
theorem interᵢ_union_of_monotone {ι α} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {s t : ι → Set α}
    (hs : Monotone s) (ht : Monotone t) : (⋂ i, s i ∪ t i) = (⋂ i, s i) ∪ ⋂ i, t i :=
  infᵢ_sup_of_monotone hs ht
#align set.Inter_union_of_monotone Set.interᵢ_union_of_monotone

/- warning: set.Inter_union_of_antitone -> Set.interᵢ_union_of_antitone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u1} ι] [_inst_2 : IsDirected.{u1} ι (LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_1))] {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u2} α)}, (Antitone.{u1, u2} ι (Set.{u2} α) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) s) -> (Antitone.{u1, u2} ι (Set.{u2} α) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) t) -> (Eq.{succ u2} (Set.{u2} α) (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => Union.union.{u2} (Set.{u2} α) (Set.hasUnion.{u2} α) (s i) (t i))) (Union.union.{u2} (Set.{u2} α) (Set.hasUnion.{u2} α) (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => t i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u2} ι] [_inst_2 : IsDirected.{u2} ι (fun (x._@.Mathlib.Data.Set.Lattice._hyg.10017 : ι) (x._@.Mathlib.Data.Set.Lattice._hyg.10019 : ι) => LE.le.{u2} ι (Preorder.toLE.{u2} ι _inst_1) x._@.Mathlib.Data.Set.Lattice._hyg.10017 x._@.Mathlib.Data.Set.Lattice._hyg.10019)] {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u1} α)}, (Antitone.{u2, u1} ι (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) s) -> (Antitone.{u2, u1} ι (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) t) -> (Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (s i) (t i))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => t i))))
Case conversion may be inaccurate. Consider using '#align set.Inter_union_of_antitone Set.interᵢ_union_of_antitoneₓ'. -/
theorem interᵢ_union_of_antitone {ι α} [Preorder ι] [IsDirected ι (· ≤ ·)] {s t : ι → Set α}
    (hs : Antitone s) (ht : Antitone t) : (⋂ i, s i ∪ t i) = (⋂ i, s i) ∪ ⋂ i, t i :=
  infᵢ_sup_of_antitone hs ht
#align set.Inter_union_of_antitone Set.interᵢ_union_of_antitone

/- warning: set.Union_Inter_subset -> Set.unionᵢ_interᵢ_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} {s : ι -> ι' -> (Set.{u1} α)}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.unionᵢ.{u1, u3} α ι' (fun (j : ι') => Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i j))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α ι' (fun (j : ι') => s i j)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u1}} {ι' : Sort.{u2}} {s : ι -> ι' -> (Set.{u3} α)}, HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (Set.unionᵢ.{u3, u2} α ι' (fun (j : ι') => Set.interᵢ.{u3, u1} α ι (fun (i : ι) => s i j))) (Set.interᵢ.{u3, u1} α ι (fun (i : ι) => Set.unionᵢ.{u3, u2} α ι' (fun (j : ι') => s i j)))
Case conversion may be inaccurate. Consider using '#align set.Union_Inter_subset Set.unionᵢ_interᵢ_subsetₓ'. -/
/-- An equality version of this lemma is `Union_Inter_of_monotone` in `data.set.finite`. -/
theorem unionᵢ_interᵢ_subset {s : ι → ι' → Set α} : (⋃ j, ⋂ i, s i j) ⊆ ⋂ i, ⋃ j, s i j :=
  supᵢ_infᵢ_le_infᵢ_supᵢ (flip s)
#align set.Union_Inter_subset Set.unionᵢ_interᵢ_subset

/- warning: set.Union_option -> Set.unionᵢ_option is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (s : (Option.{u2} ι) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α (Option.{u2} ι) (fun (o : Option.{u2} ι) => s o)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (s (Option.none.{u2} ι)) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => s (Option.some.{u2} ι i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} (s : (Option.{u2} ι) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α (Option.{u2} ι) (fun (o : Option.{u2} ι) => s o)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (s (Option.none.{u2} ι)) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => s (Option.some.{u2} ι i))))
Case conversion may be inaccurate. Consider using '#align set.Union_option Set.unionᵢ_optionₓ'. -/
theorem unionᵢ_option {ι} (s : Option ι → Set α) : (⋃ o, s o) = s none ∪ ⋃ i, s (some i) :=
  supᵢ_option s
#align set.Union_option Set.unionᵢ_option

/- warning: set.Inter_option -> Set.interᵢ_option is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (s : (Option.{u2} ι) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, succ u2} α (Option.{u2} ι) (fun (o : Option.{u2} ι) => s o)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (s (Option.none.{u2} ι)) (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => s (Option.some.{u2} ι i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} (s : (Option.{u2} ι) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, succ u2} α (Option.{u2} ι) (fun (o : Option.{u2} ι) => s o)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (s (Option.none.{u2} ι)) (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => s (Option.some.{u2} ι i))))
Case conversion may be inaccurate. Consider using '#align set.Inter_option Set.interᵢ_optionₓ'. -/
theorem interᵢ_option {ι} (s : Option ι → Set α) : (⋂ o, s o) = s none ∩ ⋂ i, s (some i) :=
  infᵢ_option s
#align set.Inter_option Set.interᵢ_option

section

variable (p : ι → Prop) [DecidablePred p]

/- warning: set.Union_dite -> Set.unionᵢ_dite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (p : ι -> Prop) [_inst_1 : DecidablePred.{u2} ι p] (f : forall (i : ι), (p i) -> (Set.{u1} α)) (g : forall (i : ι), (Not (p i)) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => dite.{succ u1} (Set.{u1} α) (p i) (_inst_1 i) (fun (h : p i) => f i h) (fun (h : Not (p i)) => g i h))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (p i) (fun (h : p i) => f i h))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Not (p i)) (fun (h : Not (p i)) => g i h))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (p : ι -> Prop) [_inst_1 : DecidablePred.{u1} ι p] (f : forall (i : ι), (p i) -> (Set.{u2} α)) (g : forall (i : ι), (Not (p i)) -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => dite.{succ u2} (Set.{u2} α) (p i) (_inst_1 i) (fun (h : p i) => f i h) (fun (h : Not (p i)) => g i h))) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (p i) (fun (h : p i) => f i h))) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Not (p i)) (fun (h : Not (p i)) => g i h))))
Case conversion may be inaccurate. Consider using '#align set.Union_dite Set.unionᵢ_diteₓ'. -/
theorem unionᵢ_dite (f : ∀ i, p i → Set α) (g : ∀ i, ¬p i → Set α) :
    (⋃ i, if h : p i then f i h else g i h) = (⋃ (i) (h : p i), f i h) ∪ ⋃ (i) (h : ¬p i), g i h :=
  supᵢ_dite _ _ _
#align set.Union_dite Set.unionᵢ_dite

/- warning: set.Union_ite -> Set.unionᵢ_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (p : ι -> Prop) [_inst_1 : DecidablePred.{u2} ι p] (f : ι -> (Set.{u1} α)) (g : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => ite.{succ u1} (Set.{u1} α) (p i) (_inst_1 i) (f i) (g i))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (p i) (fun (h : p i) => f i))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Not (p i)) (fun (h : Not (p i)) => g i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (p : ι -> Prop) [_inst_1 : DecidablePred.{u1} ι p] (f : ι -> (Set.{u2} α)) (g : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => ite.{succ u2} (Set.{u2} α) (p i) (_inst_1 i) (f i) (g i))) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (p i) (fun (h : p i) => f i))) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Not (p i)) (fun (h : Not (p i)) => g i))))
Case conversion may be inaccurate. Consider using '#align set.Union_ite Set.unionᵢ_iteₓ'. -/
theorem unionᵢ_ite (f g : ι → Set α) :
    (⋃ i, if p i then f i else g i) = (⋃ (i) (h : p i), f i) ∪ ⋃ (i) (h : ¬p i), g i :=
  unionᵢ_dite _ _ _
#align set.Union_ite Set.unionᵢ_ite

/- warning: set.Inter_dite -> Set.interᵢ_dite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (p : ι -> Prop) [_inst_1 : DecidablePred.{u2} ι p] (f : forall (i : ι), (p i) -> (Set.{u1} α)) (g : forall (i : ι), (Not (p i)) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => dite.{succ u1} (Set.{u1} α) (p i) (_inst_1 i) (fun (h : p i) => f i h) (fun (h : Not (p i)) => g i h))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (p i) (fun (h : p i) => f i h))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Not (p i)) (fun (h : Not (p i)) => g i h))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (p : ι -> Prop) [_inst_1 : DecidablePred.{u1} ι p] (f : forall (i : ι), (p i) -> (Set.{u2} α)) (g : forall (i : ι), (Not (p i)) -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => dite.{succ u2} (Set.{u2} α) (p i) (_inst_1 i) (fun (h : p i) => f i h) (fun (h : Not (p i)) => g i h))) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Set.interᵢ.{u2, 0} α (p i) (fun (h : p i) => f i h))) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Set.interᵢ.{u2, 0} α (Not (p i)) (fun (h : Not (p i)) => g i h))))
Case conversion may be inaccurate. Consider using '#align set.Inter_dite Set.interᵢ_diteₓ'. -/
theorem interᵢ_dite (f : ∀ i, p i → Set α) (g : ∀ i, ¬p i → Set α) :
    (⋂ i, if h : p i then f i h else g i h) = (⋂ (i) (h : p i), f i h) ∩ ⋂ (i) (h : ¬p i), g i h :=
  infᵢ_dite _ _ _
#align set.Inter_dite Set.interᵢ_dite

/- warning: set.Inter_ite -> Set.interᵢ_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (p : ι -> Prop) [_inst_1 : DecidablePred.{u2} ι p] (f : ι -> (Set.{u1} α)) (g : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => ite.{succ u1} (Set.{u1} α) (p i) (_inst_1 i) (f i) (g i))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (p i) (fun (h : p i) => f i))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Not (p i)) (fun (h : Not (p i)) => g i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (p : ι -> Prop) [_inst_1 : DecidablePred.{u1} ι p] (f : ι -> (Set.{u2} α)) (g : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => ite.{succ u2} (Set.{u2} α) (p i) (_inst_1 i) (f i) (g i))) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Set.interᵢ.{u2, 0} α (p i) (fun (h : p i) => f i))) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Set.interᵢ.{u2, 0} α (Not (p i)) (fun (h : Not (p i)) => g i))))
Case conversion may be inaccurate. Consider using '#align set.Inter_ite Set.interᵢ_iteₓ'. -/
theorem interᵢ_ite (f g : ι → Set α) :
    (⋂ i, if p i then f i else g i) = (⋂ (i) (h : p i), f i) ∩ ⋂ (i) (h : ¬p i), g i :=
  interᵢ_dite _ _ _
#align set.Inter_ite Set.interᵢ_ite

end

/- warning: set.image_projection_prod -> Set.image_projection_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {v : forall (i : ι), Set.{u2} (α i)}, (Set.Nonempty.{max u1 u2} (forall (i : ι), α i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) v)) -> (forall (i : ι), Eq.{succ u2} (Set.{u2} (α i)) (Set.image.{max u1 u2, u2} (forall (i : ι), α i) (α i) (fun (x : forall (i : ι), α i) => x i) (Set.interᵢ.{max u1 u2, succ u1} (forall (i : ι), α i) ι (fun (k : ι) => Set.preimage.{max u1 u2, u2} (forall (i : ι), α i) (α k) (fun (x : forall (j : ι), α j) => x k) (v k)))) (v i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {v : forall (i : ι), Set.{u1} (α i)}, (Set.Nonempty.{max u2 u1} (forall (i : ι), α i) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) v)) -> (forall (i : ι), Eq.{succ u1} (Set.{u1} (α i)) (Set.image.{max u2 u1, u1} (forall (i : ι), α i) (α i) (fun (x : forall (i : ι), α i) => x i) (Set.interᵢ.{max u2 u1, succ u2} (forall (i : ι), α i) ι (fun (k : ι) => Set.preimage.{max u2 u1, u1} (forall (i : ι), α i) (α k) (fun (x : forall (j : ι), α j) => x k) (v k)))) (v i))
Case conversion may be inaccurate. Consider using '#align set.image_projection_prod Set.image_projection_prodₓ'. -/
theorem image_projection_prod {ι : Type _} {α : ι → Type _} {v : ∀ i : ι, Set (α i)}
    (hv : (pi univ v).Nonempty) (i : ι) :
    ((fun x : ∀ i : ι, α i => x i) '' ⋂ k, (fun x : ∀ j : ι, α j => x k) ⁻¹' v k) = v i := by
  classical
    apply subset.antisymm
    · simp [Inter_subset]
    · intro y y_in
      simp only [mem_image, mem_Inter, mem_preimage]
      rcases hv with ⟨z, hz⟩
      refine' ⟨Function.update z i y, _, update_same i y z⟩
      rw [@forall_update_iff ι α _ z i y fun i t => t ∈ v i]
      exact ⟨y_in, fun j hj => by simpa using hz j⟩
#align set.image_projection_prod Set.image_projection_prod

/-! ### Unions and intersections indexed by `Prop` -/


#print Set.interᵢ_false /-
theorem interᵢ_false {s : False → Set α} : interᵢ s = univ :=
  infᵢ_false
#align set.Inter_false Set.interᵢ_false
-/

#print Set.unionᵢ_false /-
theorem unionᵢ_false {s : False → Set α} : unionᵢ s = ∅ :=
  supᵢ_false
#align set.Union_false Set.unionᵢ_false
-/

#print Set.interᵢ_true /-
@[simp]
theorem interᵢ_true {s : True → Set α} : interᵢ s = s trivial :=
  infᵢ_true
#align set.Inter_true Set.interᵢ_true
-/

#print Set.unionᵢ_true /-
@[simp]
theorem unionᵢ_true {s : True → Set α} : unionᵢ s = s trivial :=
  supᵢ_true
#align set.Union_true Set.unionᵢ_true
-/

#print Set.interᵢ_exists /-
@[simp]
theorem interᵢ_exists {p : ι → Prop} {f : Exists p → Set α} :
    (⋂ x, f x) = ⋂ (i) (h : p i), f ⟨i, h⟩ :=
  infᵢ_exists
#align set.Inter_exists Set.interᵢ_exists
-/

#print Set.unionᵢ_exists /-
@[simp]
theorem unionᵢ_exists {p : ι → Prop} {f : Exists p → Set α} :
    (⋃ x, f x) = ⋃ (i) (h : p i), f ⟨i, h⟩ :=
  supᵢ_exists
#align set.Union_exists Set.unionᵢ_exists
-/

/- warning: set.Union_empty -> Set.unionᵢ_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}}, Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}}, Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))
Case conversion may be inaccurate. Consider using '#align set.Union_empty Set.unionᵢ_emptyₓ'. -/
@[simp]
theorem unionᵢ_empty : (⋃ i : ι, ∅ : Set α) = ∅ :=
  supᵢ_bot
#align set.Union_empty Set.unionᵢ_empty

/- warning: set.Inter_univ -> Set.interᵢ_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}}, Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.univ.{u1} α)) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}}, Eq.{succ u2} (Set.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Set.univ.{u2} α)) (Set.univ.{u2} α)
Case conversion may be inaccurate. Consider using '#align set.Inter_univ Set.interᵢ_univₓ'. -/
@[simp]
theorem interᵢ_univ : (⋂ i : ι, univ : Set α) = univ :=
  infᵢ_top
#align set.Inter_univ Set.interᵢ_univ

section

variable {s : ι → Set α}

/- warning: set.Union_eq_empty -> Set.unionᵢ_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)}, Iff (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (forall (i : ι), Eq.{succ u1} (Set.{u1} α) (s i) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u2} α)}, Iff (Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i)) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (forall (i : ι), Eq.{succ u2} (Set.{u2} α) (s i) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α)))
Case conversion may be inaccurate. Consider using '#align set.Union_eq_empty Set.unionᵢ_eq_emptyₓ'. -/
@[simp]
theorem unionᵢ_eq_empty : (⋃ i, s i) = ∅ ↔ ∀ i, s i = ∅ :=
  supᵢ_eq_bot
#align set.Union_eq_empty Set.unionᵢ_eq_empty

/- warning: set.Inter_eq_univ -> Set.interᵢ_eq_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)}, Iff (Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (Set.univ.{u1} α)) (forall (i : ι), Eq.{succ u1} (Set.{u1} α) (s i) (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u2} α)}, Iff (Eq.{succ u2} (Set.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => s i)) (Set.univ.{u2} α)) (forall (i : ι), Eq.{succ u2} (Set.{u2} α) (s i) (Set.univ.{u2} α))
Case conversion may be inaccurate. Consider using '#align set.Inter_eq_univ Set.interᵢ_eq_univₓ'. -/
@[simp]
theorem interᵢ_eq_univ : (⋂ i, s i) = univ ↔ ∀ i, s i = univ :=
  infᵢ_eq_top
#align set.Inter_eq_univ Set.interᵢ_eq_univ

/- warning: set.nonempty_Union -> Set.nonempty_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)}, Iff (Set.Nonempty.{u1} α (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i))) (Exists.{u2} ι (fun (i : ι) => Set.Nonempty.{u1} α (s i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u2} α)}, Iff (Set.Nonempty.{u2} α (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i))) (Exists.{u1} ι (fun (i : ι) => Set.Nonempty.{u2} α (s i)))
Case conversion may be inaccurate. Consider using '#align set.nonempty_Union Set.nonempty_unionᵢₓ'. -/
@[simp]
theorem nonempty_unionᵢ : (⋃ i, s i).Nonempty ↔ ∃ i, (s i).Nonempty := by
  simp [nonempty_iff_ne_empty]
#align set.nonempty_Union Set.nonempty_unionᵢ

/- warning: set.nonempty_bUnion -> Set.nonempty_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t : Set.{u1} α} {s : α -> (Set.{u2} β)}, Iff (Set.Nonempty.{u2} β (Set.unionᵢ.{u2, succ u1} β α (fun (i : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) => s i)))) (Exists.{succ u1} α (fun (i : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) => Set.Nonempty.{u2} β (s i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t : Set.{u2} α} {s : α -> (Set.{u1} β)}, Iff (Set.Nonempty.{u1} β (Set.unionᵢ.{u1, succ u2} β α (fun (i : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) => s i)))) (Exists.{succ u2} α (fun (i : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) (Set.Nonempty.{u1} β (s i))))
Case conversion may be inaccurate. Consider using '#align set.nonempty_bUnion Set.nonempty_bunionᵢₓ'. -/
@[simp]
theorem nonempty_bunionᵢ {t : Set α} {s : α → Set β} :
    (⋃ i ∈ t, s i).Nonempty ↔ ∃ i ∈ t, (s i).Nonempty := by simp [nonempty_iff_ne_empty]
#align set.nonempty_bUnion Set.nonempty_bunionᵢ

/- warning: set.Union_nonempty_index -> Set.unionᵢ_nonempty_index is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : (Set.Nonempty.{u1} α s) -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, 0} β (Set.Nonempty.{u1} α s) (fun (h : Set.Nonempty.{u1} α s) => t h)) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => t (Exists.intro.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) x H))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : (Set.Nonempty.{u2} α s) -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, 0} β (Set.Nonempty.{u2} α s) (fun (h : Set.Nonempty.{u2} α s) => t h)) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => t (Exists.intro.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x H))))
Case conversion may be inaccurate. Consider using '#align set.Union_nonempty_index Set.unionᵢ_nonempty_indexₓ'. -/
theorem unionᵢ_nonempty_index (s : Set α) (t : s.Nonempty → Set β) :
    (⋃ h, t h) = ⋃ x ∈ s, t ⟨x, ‹_›⟩ :=
  supᵢ_exists
#align set.Union_nonempty_index Set.unionᵢ_nonempty_index

end

#print Set.interᵢ_interᵢ_eq_left /-
@[simp]
theorem interᵢ_interᵢ_eq_left {b : β} {s : ∀ x : β, x = b → Set α} :
    (⋂ (x) (h : x = b), s x h) = s b rfl :=
  infᵢ_infᵢ_eq_left
#align set.Inter_Inter_eq_left Set.interᵢ_interᵢ_eq_left
-/

#print Set.interᵢ_interᵢ_eq_right /-
@[simp]
theorem interᵢ_interᵢ_eq_right {b : β} {s : ∀ x : β, b = x → Set α} :
    (⋂ (x) (h : b = x), s x h) = s b rfl :=
  infᵢ_infᵢ_eq_right
#align set.Inter_Inter_eq_right Set.interᵢ_interᵢ_eq_right
-/

#print Set.unionᵢ_unionᵢ_eq_left /-
@[simp]
theorem unionᵢ_unionᵢ_eq_left {b : β} {s : ∀ x : β, x = b → Set α} :
    (⋃ (x) (h : x = b), s x h) = s b rfl :=
  supᵢ_supᵢ_eq_left
#align set.Union_Union_eq_left Set.unionᵢ_unionᵢ_eq_left
-/

#print Set.unionᵢ_unionᵢ_eq_right /-
@[simp]
theorem unionᵢ_unionᵢ_eq_right {b : β} {s : ∀ x : β, b = x → Set α} :
    (⋃ (x) (h : b = x), s x h) = s b rfl :=
  supᵢ_supᵢ_eq_right
#align set.Union_Union_eq_right Set.unionᵢ_unionᵢ_eq_right
-/

/- warning: set.Inter_or -> Set.interᵢ_or is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : Prop} {q : Prop} (s : (Or p q) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, 0} α (Or p q) (fun (h : Or p q) => s h)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.interᵢ.{u1, 0} α p (fun (h : p) => s (Or.inl p q h))) (Set.interᵢ.{u1, 0} α q (fun (h : q) => s (Or.inr p q h))))
but is expected to have type
  forall {α : Type.{u1}} {p : Prop} {q : Prop} (s : (Or p q) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, 0} α (Or p q) (fun (h : Or p q) => s h)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.interᵢ.{u1, 0} α p (fun (h : p) => s (Or.inl p q h))) (Set.interᵢ.{u1, 0} α q (fun (h : q) => s (Or.inr p q h))))
Case conversion may be inaccurate. Consider using '#align set.Inter_or Set.interᵢ_orₓ'. -/
theorem interᵢ_or {p q : Prop} (s : p ∨ q → Set α) :
    (⋂ h, s h) = (⋂ h : p, s (Or.inl h)) ∩ ⋂ h : q, s (Or.inr h) :=
  infᵢ_or
#align set.Inter_or Set.interᵢ_or

/- warning: set.Union_or -> Set.unionᵢ_or is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : Prop} {q : Prop} (s : (Or p q) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, 0} α (Or p q) (fun (h : Or p q) => s h)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Set.unionᵢ.{u1, 0} α p (fun (i : p) => s (Or.inl p q i))) (Set.unionᵢ.{u1, 0} α q (fun (j : q) => s (Or.inr p q j))))
but is expected to have type
  forall {α : Type.{u1}} {p : Prop} {q : Prop} (s : (Or p q) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, 0} α (Or p q) (fun (h : Or p q) => s h)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Set.unionᵢ.{u1, 0} α p (fun (i : p) => s (Or.inl p q i))) (Set.unionᵢ.{u1, 0} α q (fun (j : q) => s (Or.inr p q j))))
Case conversion may be inaccurate. Consider using '#align set.Union_or Set.unionᵢ_orₓ'. -/
theorem unionᵢ_or {p q : Prop} (s : p ∨ q → Set α) :
    (⋃ h, s h) = (⋃ i, s (Or.inl i)) ∪ ⋃ j, s (Or.inr j) :=
  supᵢ_or
#align set.Union_or Set.unionᵢ_or

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (hp hq) -/
#print Set.unionᵢ_and /-
theorem unionᵢ_and {p q : Prop} (s : p ∧ q → Set α) : (⋃ h, s h) = ⋃ (hp) (hq), s ⟨hp, hq⟩ :=
  supᵢ_and
#align set.Union_and Set.unionᵢ_and
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (hp hq) -/
#print Set.interᵢ_and /-
theorem interᵢ_and {p q : Prop} (s : p ∧ q → Set α) : (⋂ h, s h) = ⋂ (hp) (hq), s ⟨hp, hq⟩ :=
  infᵢ_and
#align set.Inter_and Set.interᵢ_and
-/

/- warning: set.Union_comm -> Set.unionᵢ_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} (s : ι -> ι' -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α ι' (fun (i' : ι') => s i i'))) (Set.unionᵢ.{u1, u3} α ι' (fun (i' : ι') => Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i i')))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} (s : ι -> ι' -> (Set.{u3} α)), Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α ι' (fun (i' : ι') => s i i'))) (Set.unionᵢ.{u3, u1} α ι' (fun (i' : ι') => Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => s i i')))
Case conversion may be inaccurate. Consider using '#align set.Union_comm Set.unionᵢ_commₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i i') -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' i) -/
theorem unionᵢ_comm (s : ι → ι' → Set α) : (⋃ (i) (i'), s i i') = ⋃ (i') (i), s i i' :=
  supᵢ_comm
#align set.Union_comm Set.unionᵢ_comm

/- warning: set.Inter_comm -> Set.interᵢ_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} (s : ι -> ι' -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α ι' (fun (i' : ι') => s i i'))) (Set.interᵢ.{u1, u3} α ι' (fun (i' : ι') => Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i i')))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} (s : ι -> ι' -> (Set.{u3} α)), Eq.{succ u3} (Set.{u3} α) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α ι' (fun (i' : ι') => s i i'))) (Set.interᵢ.{u3, u1} α ι' (fun (i' : ι') => Set.interᵢ.{u3, u2} α ι (fun (i : ι) => s i i')))
Case conversion may be inaccurate. Consider using '#align set.Inter_comm Set.interᵢ_commₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i i') -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' i) -/
theorem interᵢ_comm (s : ι → ι' → Set α) : (⋂ (i) (i'), s i i') = ⋂ (i') (i), s i i' :=
  infᵢ_comm
#align set.Inter_comm Set.interᵢ_comm

/- warning: set.Union₂_comm -> Set.unionᵢ₂_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ₁ : ι -> Sort.{u3}} {κ₂ : ι -> Sort.{u4}} (s : forall (i₁ : ι), (κ₁ i₁) -> (forall (i₂ : ι), (κ₂ i₂) -> (Set.{u1} α))), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i₁ : ι) => Set.unionᵢ.{u1, u3} α (κ₁ i₁) (fun (j₁ : κ₁ i₁) => Set.unionᵢ.{u1, u2} α ι (fun (i₂ : ι) => Set.unionᵢ.{u1, u4} α (κ₂ i₂) (fun (j₂ : κ₂ i₂) => s i₁ j₁ i₂ j₂))))) (Set.unionᵢ.{u1, u2} α ι (fun (i₂ : ι) => Set.unionᵢ.{u1, u4} α (κ₂ i₂) (fun (j₂ : κ₂ i₂) => Set.unionᵢ.{u1, u2} α ι (fun (i₁ : ι) => Set.unionᵢ.{u1, u3} α (κ₁ i₁) (fun (j₁ : κ₁ i₁) => s i₁ j₁ i₂ j₂)))))
but is expected to have type
  forall {α : Type.{u4}} {ι : Sort.{u3}} {κ₁ : ι -> Sort.{u2}} {κ₂ : ι -> Sort.{u1}} (s : forall (i₁ : ι), (κ₁ i₁) -> (forall (i₂ : ι), (κ₂ i₂) -> (Set.{u4} α))), Eq.{succ u4} (Set.{u4} α) (Set.unionᵢ.{u4, u3} α ι (fun (i₁ : ι) => Set.unionᵢ.{u4, u2} α (κ₁ i₁) (fun (j₁ : κ₁ i₁) => Set.unionᵢ.{u4, u3} α ι (fun (i₂ : ι) => Set.unionᵢ.{u4, u1} α (κ₂ i₂) (fun (j₂ : κ₂ i₂) => s i₁ j₁ i₂ j₂))))) (Set.unionᵢ.{u4, u3} α ι (fun (i₂ : ι) => Set.unionᵢ.{u4, u1} α (κ₂ i₂) (fun (j₂ : κ₂ i₂) => Set.unionᵢ.{u4, u3} α ι (fun (i₁ : ι) => Set.unionᵢ.{u4, u2} α (κ₁ i₁) (fun (j₁ : κ₁ i₁) => s i₁ j₁ i₂ j₂)))))
Case conversion may be inaccurate. Consider using '#align set.Union₂_comm Set.unionᵢ₂_commₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₁ j₁ i₂ j₂) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₂ j₂ i₁ j₁) -/
theorem unionᵢ₂_comm (s : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Set α) :
    (⋃ (i₁) (j₁) (i₂) (j₂), s i₁ j₁ i₂ j₂) = ⋃ (i₂) (j₂) (i₁) (j₁), s i₁ j₁ i₂ j₂ :=
  supᵢ₂_comm _
#align set.Union₂_comm Set.unionᵢ₂_comm

/- warning: set.Inter₂_comm -> Set.interᵢ₂_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ₁ : ι -> Sort.{u3}} {κ₂ : ι -> Sort.{u4}} (s : forall (i₁ : ι), (κ₁ i₁) -> (forall (i₂ : ι), (κ₂ i₂) -> (Set.{u1} α))), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i₁ : ι) => Set.interᵢ.{u1, u3} α (κ₁ i₁) (fun (j₁ : κ₁ i₁) => Set.interᵢ.{u1, u2} α ι (fun (i₂ : ι) => Set.interᵢ.{u1, u4} α (κ₂ i₂) (fun (j₂ : κ₂ i₂) => s i₁ j₁ i₂ j₂))))) (Set.interᵢ.{u1, u2} α ι (fun (i₂ : ι) => Set.interᵢ.{u1, u4} α (κ₂ i₂) (fun (j₂ : κ₂ i₂) => Set.interᵢ.{u1, u2} α ι (fun (i₁ : ι) => Set.interᵢ.{u1, u3} α (κ₁ i₁) (fun (j₁ : κ₁ i₁) => s i₁ j₁ i₂ j₂)))))
but is expected to have type
  forall {α : Type.{u4}} {ι : Sort.{u3}} {κ₁ : ι -> Sort.{u2}} {κ₂ : ι -> Sort.{u1}} (s : forall (i₁ : ι), (κ₁ i₁) -> (forall (i₂ : ι), (κ₂ i₂) -> (Set.{u4} α))), Eq.{succ u4} (Set.{u4} α) (Set.interᵢ.{u4, u3} α ι (fun (i₁ : ι) => Set.interᵢ.{u4, u2} α (κ₁ i₁) (fun (j₁ : κ₁ i₁) => Set.interᵢ.{u4, u3} α ι (fun (i₂ : ι) => Set.interᵢ.{u4, u1} α (κ₂ i₂) (fun (j₂ : κ₂ i₂) => s i₁ j₁ i₂ j₂))))) (Set.interᵢ.{u4, u3} α ι (fun (i₂ : ι) => Set.interᵢ.{u4, u1} α (κ₂ i₂) (fun (j₂ : κ₂ i₂) => Set.interᵢ.{u4, u3} α ι (fun (i₁ : ι) => Set.interᵢ.{u4, u2} α (κ₁ i₁) (fun (j₁ : κ₁ i₁) => s i₁ j₁ i₂ j₂)))))
Case conversion may be inaccurate. Consider using '#align set.Inter₂_comm Set.interᵢ₂_commₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₁ j₁ i₂ j₂) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₂ j₂ i₁ j₁) -/
theorem interᵢ₂_comm (s : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Set α) :
    (⋂ (i₁) (j₁) (i₂) (j₂), s i₁ j₁ i₂ j₂) = ⋂ (i₂) (j₂) (i₁) (j₁), s i₁ j₁ i₂ j₂ :=
  infᵢ₂_comm _
#align set.Inter₂_comm Set.interᵢ₂_comm

/- warning: set.bUnion_and -> Set.bunionᵢ_and is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} (p : ι -> Prop) (q : ι -> ι' -> Prop) (s : forall (x : ι) (y : ι'), (And (p x) (q x y)) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (x : ι) => Set.unionᵢ.{u1, u3} α ι' (fun (y : ι') => Set.unionᵢ.{u1, 0} α (And (p x) (q x y)) (fun (h : And (p x) (q x y)) => s x y h)))) (Set.unionᵢ.{u1, u2} α ι (fun (x : ι) => Set.unionᵢ.{u1, 0} α (p x) (fun (hx : p x) => Set.unionᵢ.{u1, u3} α ι' (fun (y : ι') => Set.unionᵢ.{u1, 0} α (q x y) (fun (hy : q x y) => s x y (And.intro (p x) (q x y) hx hy))))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} (p : ι -> Prop) (q : ι -> ι' -> Prop) (s : forall (x : ι) (y : ι'), (And (p x) (q x y)) -> (Set.{u3} α)), Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, u2} α ι (fun (x : ι) => Set.unionᵢ.{u3, u1} α ι' (fun (y : ι') => Set.unionᵢ.{u3, 0} α (And (p x) (q x y)) (fun (h : And (p x) (q x y)) => s x y h)))) (Set.unionᵢ.{u3, u2} α ι (fun (x : ι) => Set.unionᵢ.{u3, 0} α (p x) (fun (hx : p x) => Set.unionᵢ.{u3, u1} α ι' (fun (y : ι') => Set.unionᵢ.{u3, 0} α (q x y) (fun (hy : q x y) => s x y (And.intro (p x) (q x y) hx hy))))))
Case conversion may be inaccurate. Consider using '#align set.bUnion_and Set.bunionᵢ_andₓ'. -/
@[simp]
theorem bunionᵢ_and (p : ι → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p x ∧ q x y → Set α) :
    (⋃ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h) =
      ⋃ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ :=
  by simp only [Union_and, @Union_comm _ ι']
#align set.bUnion_and Set.bunionᵢ_and

/- warning: set.bUnion_and' -> Set.bunionᵢ_and' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s : forall (x : ι) (y : ι'), (And (p y) (q x y)) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (x : ι) => Set.unionᵢ.{u1, u3} α ι' (fun (y : ι') => Set.unionᵢ.{u1, 0} α (And (p y) (q x y)) (fun (h : And (p y) (q x y)) => s x y h)))) (Set.unionᵢ.{u1, u3} α ι' (fun (y : ι') => Set.unionᵢ.{u1, 0} α (p y) (fun (hy : p y) => Set.unionᵢ.{u1, u2} α ι (fun (x : ι) => Set.unionᵢ.{u1, 0} α (q x y) (fun (hx : q x y) => s x y (And.intro (p y) (q x y) hy hx))))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s : forall (x : ι) (y : ι'), (And (p y) (q x y)) -> (Set.{u3} α)), Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, u2} α ι (fun (x : ι) => Set.unionᵢ.{u3, u1} α ι' (fun (y : ι') => Set.unionᵢ.{u3, 0} α (And (p y) (q x y)) (fun (h : And (p y) (q x y)) => s x y h)))) (Set.unionᵢ.{u3, u1} α ι' (fun (y : ι') => Set.unionᵢ.{u3, 0} α (p y) (fun (hy : p y) => Set.unionᵢ.{u3, u2} α ι (fun (x : ι) => Set.unionᵢ.{u3, 0} α (q x y) (fun (hx : q x y) => s x y (And.intro (p y) (q x y) hy hx))))))
Case conversion may be inaccurate. Consider using '#align set.bUnion_and' Set.bunionᵢ_and'ₓ'. -/
@[simp]
theorem bunionᵢ_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p y ∧ q x y → Set α) :
    (⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h) =
      ⋃ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ :=
  by simp only [Union_and, @Union_comm _ ι]
#align set.bUnion_and' Set.bunionᵢ_and'

/- warning: set.bInter_and -> Set.binterᵢ_and is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} (p : ι -> Prop) (q : ι -> ι' -> Prop) (s : forall (x : ι) (y : ι'), (And (p x) (q x y)) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (x : ι) => Set.interᵢ.{u1, u3} α ι' (fun (y : ι') => Set.interᵢ.{u1, 0} α (And (p x) (q x y)) (fun (h : And (p x) (q x y)) => s x y h)))) (Set.interᵢ.{u1, u2} α ι (fun (x : ι) => Set.interᵢ.{u1, 0} α (p x) (fun (hx : p x) => Set.interᵢ.{u1, u3} α ι' (fun (y : ι') => Set.interᵢ.{u1, 0} α (q x y) (fun (hy : q x y) => s x y (And.intro (p x) (q x y) hx hy))))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} (p : ι -> Prop) (q : ι -> ι' -> Prop) (s : forall (x : ι) (y : ι'), (And (p x) (q x y)) -> (Set.{u3} α)), Eq.{succ u3} (Set.{u3} α) (Set.interᵢ.{u3, u2} α ι (fun (x : ι) => Set.interᵢ.{u3, u1} α ι' (fun (y : ι') => Set.interᵢ.{u3, 0} α (And (p x) (q x y)) (fun (h : And (p x) (q x y)) => s x y h)))) (Set.interᵢ.{u3, u2} α ι (fun (x : ι) => Set.interᵢ.{u3, 0} α (p x) (fun (hx : p x) => Set.interᵢ.{u3, u1} α ι' (fun (y : ι') => Set.interᵢ.{u3, 0} α (q x y) (fun (hy : q x y) => s x y (And.intro (p x) (q x y) hx hy))))))
Case conversion may be inaccurate. Consider using '#align set.bInter_and Set.binterᵢ_andₓ'. -/
@[simp]
theorem binterᵢ_and (p : ι → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p x ∧ q x y → Set α) :
    (⋂ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h) =
      ⋂ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ :=
  by simp only [Inter_and, @Inter_comm _ ι']
#align set.bInter_and Set.binterᵢ_and

/- warning: set.bInter_and' -> Set.binterᵢ_and' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s : forall (x : ι) (y : ι'), (And (p y) (q x y)) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (x : ι) => Set.interᵢ.{u1, u3} α ι' (fun (y : ι') => Set.interᵢ.{u1, 0} α (And (p y) (q x y)) (fun (h : And (p y) (q x y)) => s x y h)))) (Set.interᵢ.{u1, u3} α ι' (fun (y : ι') => Set.interᵢ.{u1, 0} α (p y) (fun (hy : p y) => Set.interᵢ.{u1, u2} α ι (fun (x : ι) => Set.interᵢ.{u1, 0} α (q x y) (fun (hx : q x y) => s x y (And.intro (p y) (q x y) hy hx))))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s : forall (x : ι) (y : ι'), (And (p y) (q x y)) -> (Set.{u3} α)), Eq.{succ u3} (Set.{u3} α) (Set.interᵢ.{u3, u2} α ι (fun (x : ι) => Set.interᵢ.{u3, u1} α ι' (fun (y : ι') => Set.interᵢ.{u3, 0} α (And (p y) (q x y)) (fun (h : And (p y) (q x y)) => s x y h)))) (Set.interᵢ.{u3, u1} α ι' (fun (y : ι') => Set.interᵢ.{u3, 0} α (p y) (fun (hy : p y) => Set.interᵢ.{u3, u2} α ι (fun (x : ι) => Set.interᵢ.{u3, 0} α (q x y) (fun (hx : q x y) => s x y (And.intro (p y) (q x y) hy hx))))))
Case conversion may be inaccurate. Consider using '#align set.bInter_and' Set.binterᵢ_and'ₓ'. -/
@[simp]
theorem binterᵢ_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p y ∧ q x y → Set α) :
    (⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h) =
      ⋂ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ :=
  by simp only [Inter_and, @Inter_comm _ ι]
#align set.bInter_and' Set.binterᵢ_and'

/- warning: set.Union_Union_eq_or_left -> Set.unionᵢ_unionᵢ_eq_or_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {b : β} {p : β -> Prop} {s : forall (x : β), (Or (Eq.{succ u2} β x b) (p x)) -> (Set.{u1} α)}, Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α β (fun (x : β) => Set.unionᵢ.{u1, 0} α (Or (Eq.{succ u2} β x b) (p x)) (fun (h : Or (Eq.{succ u2} β x b) (p x)) => s x h))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (s b (Or.inl (Eq.{succ u2} β b b) (p b) (rfl.{succ u2} β b))) (Set.unionᵢ.{u1, succ u2} α β (fun (x : β) => Set.unionᵢ.{u1, 0} α (p x) (fun (h : p x) => s x (Or.inr (Eq.{succ u2} β x b) (p x) h)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {b : β} {p : β -> Prop} {s : forall (x : β), (Or (Eq.{succ u2} β x b) (p x)) -> (Set.{u1} α)}, Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α β (fun (x : β) => Set.unionᵢ.{u1, 0} α (Or (Eq.{succ u2} β x b) (p x)) (fun (h : Or (Eq.{succ u2} β x b) (p x)) => s x h))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (s b (Or.inl (Eq.{succ u2} β b b) (p b) (rfl.{succ u2} β b))) (Set.unionᵢ.{u1, succ u2} α β (fun (x : β) => Set.unionᵢ.{u1, 0} α (p x) (fun (h : p x) => s x (Or.inr (Eq.{succ u2} β x b) (p x) h)))))
Case conversion may be inaccurate. Consider using '#align set.Union_Union_eq_or_left Set.unionᵢ_unionᵢ_eq_or_leftₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x h) -/
@[simp]
theorem unionᵢ_unionᵢ_eq_or_left {b : β} {p : β → Prop} {s : ∀ x : β, x = b ∨ p x → Set α} :
    (⋃ (x) (h), s x h) = s b (Or.inl rfl) ∪ ⋃ (x) (h : p x), s x (Or.inr h) := by
  simp only [Union_or, Union_union_distrib, Union_Union_eq_left]
#align set.Union_Union_eq_or_left Set.unionᵢ_unionᵢ_eq_or_left

/- warning: set.Inter_Inter_eq_or_left -> Set.interᵢ_interᵢ_eq_or_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {b : β} {p : β -> Prop} {s : forall (x : β), (Or (Eq.{succ u2} β x b) (p x)) -> (Set.{u1} α)}, Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, succ u2} α β (fun (x : β) => Set.interᵢ.{u1, 0} α (Or (Eq.{succ u2} β x b) (p x)) (fun (h : Or (Eq.{succ u2} β x b) (p x)) => s x h))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (s b (Or.inl (Eq.{succ u2} β b b) (p b) (rfl.{succ u2} β b))) (Set.interᵢ.{u1, succ u2} α β (fun (x : β) => Set.interᵢ.{u1, 0} α (p x) (fun (h : p x) => s x (Or.inr (Eq.{succ u2} β x b) (p x) h)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {b : β} {p : β -> Prop} {s : forall (x : β), (Or (Eq.{succ u2} β x b) (p x)) -> (Set.{u1} α)}, Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, succ u2} α β (fun (x : β) => Set.interᵢ.{u1, 0} α (Or (Eq.{succ u2} β x b) (p x)) (fun (h : Or (Eq.{succ u2} β x b) (p x)) => s x h))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (s b (Or.inl (Eq.{succ u2} β b b) (p b) (rfl.{succ u2} β b))) (Set.interᵢ.{u1, succ u2} α β (fun (x : β) => Set.interᵢ.{u1, 0} α (p x) (fun (h : p x) => s x (Or.inr (Eq.{succ u2} β x b) (p x) h)))))
Case conversion may be inaccurate. Consider using '#align set.Inter_Inter_eq_or_left Set.interᵢ_interᵢ_eq_or_leftₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x h) -/
@[simp]
theorem interᵢ_interᵢ_eq_or_left {b : β} {p : β → Prop} {s : ∀ x : β, x = b ∨ p x → Set α} :
    (⋂ (x) (h), s x h) = s b (Or.inl rfl) ∩ ⋂ (x) (h : p x), s x (Or.inr h) := by
  simp only [Inter_or, Inter_inter_distrib, Inter_Inter_eq_left]
#align set.Inter_Inter_eq_or_left Set.interᵢ_interᵢ_eq_or_left

/-! ### Bounded unions and intersections -/


/- warning: set.mem_bUnion -> Set.mem_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : α -> (Set.{u2} β)} {x : α} {y : β}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (t x)) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => t x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : α -> (Set.{u1} β)} {x : α} {y : β}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (t x)) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => t x))))
Case conversion may be inaccurate. Consider using '#align set.mem_bUnion Set.mem_bunionᵢₓ'. -/
/-- A specialization of `mem_Union₂`. -/
theorem mem_bunionᵢ {s : Set α} {t : α → Set β} {x : α} {y : β} (xs : x ∈ s) (ytx : y ∈ t x) :
    y ∈ ⋃ x ∈ s, t x :=
  mem_unionᵢ₂_of_mem xs ytx
#align set.mem_bUnion Set.mem_bunionᵢ

/- warning: set.mem_bInter -> Set.mem_binterᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : α -> (Set.{u2} β)} {y : β}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (t x))) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => t x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : α -> (Set.{u1} β)} {y : β}, (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (t x))) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (Set.interᵢ.{u1, succ u2} β α (fun (x : α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => t x))))
Case conversion may be inaccurate. Consider using '#align set.mem_bInter Set.mem_binterᵢₓ'. -/
/-- A specialization of `mem_Inter₂`. -/
theorem mem_binterᵢ {s : Set α} {t : α → Set β} {y : β} (h : ∀ x ∈ s, y ∈ t x) : y ∈ ⋂ x ∈ s, t x :=
  mem_interᵢ₂_of_mem h
#align set.mem_bInter Set.mem_binterᵢ

/- warning: set.subset_bUnion_of_mem -> Set.subset_bunionᵢ_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {u : α -> (Set.{u2} β)} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (u x) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => u x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {u : α -> (Set.{u1} β)} {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (u x) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => u x))))
Case conversion may be inaccurate. Consider using '#align set.subset_bUnion_of_mem Set.subset_bunionᵢ_of_memₓ'. -/
/-- A specialization of `subset_Union₂`. -/
theorem subset_bunionᵢ_of_mem {s : Set α} {u : α → Set β} {x : α} (xs : x ∈ s) :
    u x ⊆ ⋃ x ∈ s, u x :=
  subset_unionᵢ₂ x xs
#align set.subset_bUnion_of_mem Set.subset_bunionᵢ_of_mem

/- warning: set.bInter_subset_of_mem -> Set.binterᵢ_subset_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : α -> (Set.{u2} β)} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => t x))) (t x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : α -> (Set.{u1} β)} {x : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.interᵢ.{u1, succ u2} β α (fun (x : α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => t x))) (t x))
Case conversion may be inaccurate. Consider using '#align set.bInter_subset_of_mem Set.binterᵢ_subset_of_memₓ'. -/
/-- A specialization of `Inter₂_subset`. -/
theorem binterᵢ_subset_of_mem {s : Set α} {t : α → Set β} {x : α} (xs : x ∈ s) :
    (⋂ x ∈ s, t x) ⊆ t x :=
  interᵢ₂_subset x xs
#align set.bInter_subset_of_mem Set.binterᵢ_subset_of_mem

/- warning: set.bUnion_subset_bUnion_left -> Set.bunionᵢ_subset_bunionᵢ_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s' : Set.{u1} α} {t : α -> (Set.{u2} β)}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s s') -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => t x))) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s') (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s') => t x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s' : Set.{u2} α} {t : α -> (Set.{u1} β)}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s s') -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => t x))) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s') (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s') => t x))))
Case conversion may be inaccurate. Consider using '#align set.bUnion_subset_bUnion_left Set.bunionᵢ_subset_bunionᵢ_leftₓ'. -/
theorem bunionᵢ_subset_bunionᵢ_left {s s' : Set α} {t : α → Set β} (h : s ⊆ s') :
    (⋃ x ∈ s, t x) ⊆ ⋃ x ∈ s', t x :=
  Union₂_subset fun x hx => subset_bUnion_of_mem <| h hx
#align set.bUnion_subset_bUnion_left Set.bunionᵢ_subset_bunionᵢ_left

/- warning: set.bInter_subset_bInter_left -> Set.binterᵢ_subset_binterᵢ_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s' : Set.{u1} α} {t : α -> (Set.{u2} β)}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s' s) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => t x))) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s') (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s') => t x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s' : Set.{u2} α} {t : α -> (Set.{u1} β)}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s' s) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.interᵢ.{u1, succ u2} β α (fun (x : α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => t x))) (Set.interᵢ.{u1, succ u2} β α (fun (x : α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s') (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s') => t x))))
Case conversion may be inaccurate. Consider using '#align set.bInter_subset_bInter_left Set.binterᵢ_subset_binterᵢ_leftₓ'. -/
theorem binterᵢ_subset_binterᵢ_left {s s' : Set α} {t : α → Set β} (h : s' ⊆ s) :
    (⋂ x ∈ s, t x) ⊆ ⋂ x ∈ s', t x :=
  subset_Inter₂ fun x hx => bInter_subset_of_mem <| h hx
#align set.bInter_subset_bInter_left Set.binterᵢ_subset_binterᵢ_left

/- warning: set.bUnion_mono -> Set.bunionᵢ_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s' : Set.{u1} α} {t : α -> (Set.{u2} β)} {t' : α -> (Set.{u2} β)}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s' s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (t x) (t' x))) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s') (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s') => t x))) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => t' x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s' : Set.{u2} α} {t : α -> (Set.{u1} β)} {t' : α -> (Set.{u1} β)}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s' s) -> (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (t x) (t' x))) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s') (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s') => t x))) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => t' x))))
Case conversion may be inaccurate. Consider using '#align set.bUnion_mono Set.bunionᵢ_monoₓ'. -/
theorem bunionᵢ_mono {s s' : Set α} {t t' : α → Set β} (hs : s' ⊆ s) (h : ∀ x ∈ s, t x ⊆ t' x) :
    (⋃ x ∈ s', t x) ⊆ ⋃ x ∈ s, t' x :=
  (bunionᵢ_subset_bunionᵢ_left hs).trans <| unionᵢ₂_mono h
#align set.bUnion_mono Set.bunionᵢ_mono

/- warning: set.bInter_mono -> Set.binterᵢ_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s' : Set.{u1} α} {t : α -> (Set.{u2} β)} {t' : α -> (Set.{u2} β)}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s s') -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (t x) (t' x))) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s') (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s') => t x))) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => t' x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s' : Set.{u2} α} {t : α -> (Set.{u1} β)} {t' : α -> (Set.{u1} β)}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s s') -> (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (t x) (t' x))) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.interᵢ.{u1, succ u2} β α (fun (x : α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s') (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s') => t x))) (Set.interᵢ.{u1, succ u2} β α (fun (x : α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => t' x))))
Case conversion may be inaccurate. Consider using '#align set.bInter_mono Set.binterᵢ_monoₓ'. -/
theorem binterᵢ_mono {s s' : Set α} {t t' : α → Set β} (hs : s ⊆ s') (h : ∀ x ∈ s, t x ⊆ t' x) :
    (⋂ x ∈ s', t x) ⊆ ⋂ x ∈ s, t' x :=
  (binterᵢ_subset_binterᵢ_left hs).trans <| interᵢ₂_mono h
#align set.bInter_mono Set.binterᵢ_mono

/- warning: set.bUnion_eq_Union -> Set.bunionᵢ_eq_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => t x H))) (Set.unionᵢ.{u2, succ u1} β (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => t ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x) (Subtype.property.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => t x H))) (Set.unionᵢ.{u1, succ u2} β (Set.Elem.{u2} α s) (fun (x : Set.Elem.{u2} α s) => t (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x) (Subtype.property.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x)))
Case conversion may be inaccurate. Consider using '#align set.bUnion_eq_Union Set.bunionᵢ_eq_unionᵢₓ'. -/
theorem bunionᵢ_eq_unionᵢ (s : Set α) (t : ∀ x ∈ s, Set β) :
    (⋃ x ∈ s, t x ‹_›) = ⋃ x : s, t x x.2 :=
  supᵢ_subtype'
#align set.bUnion_eq_Union Set.bunionᵢ_eq_unionᵢ

/- warning: set.bInter_eq_Inter -> Set.binterᵢ_eq_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => t x H))) (Set.interᵢ.{u2, succ u1} β (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => t ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x) (Subtype.property.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.interᵢ.{u1, succ u2} β α (fun (x : α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => t x H))) (Set.interᵢ.{u1, succ u2} β (Set.Elem.{u2} α s) (fun (x : Set.Elem.{u2} α s) => t (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x) (Subtype.property.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x)))
Case conversion may be inaccurate. Consider using '#align set.bInter_eq_Inter Set.binterᵢ_eq_interᵢₓ'. -/
theorem binterᵢ_eq_interᵢ (s : Set α) (t : ∀ x ∈ s, Set β) :
    (⋂ x ∈ s, t x ‹_›) = ⋂ x : s, t x x.2 :=
  infᵢ_subtype'
#align set.bInter_eq_Inter Set.binterᵢ_eq_interᵢ

/- warning: set.Union_subtype -> Set.unionᵢ_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : α -> Prop) (s : (Subtype.{succ u1} α (fun (x : α) => p x)) -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β (Subtype.{succ u1} α (fun (x : α) => p x)) (fun (x : Subtype.{succ u1} α (fun (x : α) => p x)) => s x)) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (p x) (fun (hx : p x) => s (Subtype.mk.{succ u1} α (fun (x : α) => p x) x hx))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (p : α -> Prop) (s : (Subtype.{succ u2} α (fun (x : α) => p x)) -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, succ u2} β (Subtype.{succ u2} α (fun (x : α) => p x)) (fun (x : Subtype.{succ u2} α (fun (x : α) => p x)) => s x)) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (p x) (fun (hx : p x) => s (Subtype.mk.{succ u2} α (fun (x : α) => p x) x hx))))
Case conversion may be inaccurate. Consider using '#align set.Union_subtype Set.unionᵢ_subtypeₓ'. -/
theorem unionᵢ_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    (⋃ x : { x // p x }, s x) = ⋃ (x) (hx : p x), s ⟨x, hx⟩ :=
  supᵢ_subtype
#align set.Union_subtype Set.unionᵢ_subtype

/- warning: set.Inter_subtype -> Set.interᵢ_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : α -> Prop) (s : (Subtype.{succ u1} α (fun (x : α) => p x)) -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, succ u1} β (Subtype.{succ u1} α (fun (x : α) => p x)) (fun (x : Subtype.{succ u1} α (fun (x : α) => p x)) => s x)) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (p x) (fun (hx : p x) => s (Subtype.mk.{succ u1} α (fun (x : α) => p x) x hx))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (p : α -> Prop) (s : (Subtype.{succ u2} α (fun (x : α) => p x)) -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.interᵢ.{u1, succ u2} β (Subtype.{succ u2} α (fun (x : α) => p x)) (fun (x : Subtype.{succ u2} α (fun (x : α) => p x)) => s x)) (Set.interᵢ.{u1, succ u2} β α (fun (x : α) => Set.interᵢ.{u1, 0} β (p x) (fun (hx : p x) => s (Subtype.mk.{succ u2} α (fun (x : α) => p x) x hx))))
Case conversion may be inaccurate. Consider using '#align set.Inter_subtype Set.interᵢ_subtypeₓ'. -/
theorem interᵢ_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    (⋂ x : { x // p x }, s x) = ⋂ (x) (hx : p x), s ⟨x, hx⟩ :=
  infᵢ_subtype
#align set.Inter_subtype Set.interᵢ_subtype

#print Set.binterᵢ_empty /-
theorem binterᵢ_empty (u : α → Set β) : (⋂ x ∈ (∅ : Set α), u x) = univ :=
  infᵢ_emptyset
#align set.bInter_empty Set.binterᵢ_empty
-/

#print Set.binterᵢ_univ /-
theorem binterᵢ_univ (u : α → Set β) : (⋂ x ∈ @univ α, u x) = ⋂ x, u x :=
  infᵢ_univ
#align set.bInter_univ Set.binterᵢ_univ
-/

#print Set.bunionᵢ_self /-
@[simp]
theorem bunionᵢ_self (s : Set α) : (⋃ x ∈ s, s) = s :=
  Subset.antisymm (Union₂_subset fun x hx => Subset.refl s) fun x hx => mem_bunionᵢ hx hx
#align set.bUnion_self Set.bunionᵢ_self
-/

#print Set.unionᵢ_nonempty_self /-
@[simp]
theorem unionᵢ_nonempty_self (s : Set α) : (⋃ h : s.Nonempty, s) = s := by
  rw [Union_nonempty_index, bUnion_self]
#align set.Union_nonempty_self Set.unionᵢ_nonempty_self
-/

#print Set.binterᵢ_singleton /-
-- TODO(Jeremy): here is an artifact of the encoding of bounded intersection:
-- without dsimp, the next theorem fails to type check, because there is a lambda
-- in a type that needs to be contracted. Using simp [eq_of_mem_singleton xa] also works.
theorem binterᵢ_singleton (a : α) (s : α → Set β) : (⋂ x ∈ ({a} : Set α), s x) = s a :=
  infᵢ_singleton
#align set.bInter_singleton Set.binterᵢ_singleton
-/

/- warning: set.bInter_union -> Set.binterᵢ_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : Set.{u1} α) (u : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) => u x))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => u x))) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) => u x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : Set.{u2} α) (u : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.interᵢ.{u1, succ u2} β α (fun (x : α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) => u x))) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (Set.interᵢ.{u1, succ u2} β α (fun (x : α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => u x))) (Set.interᵢ.{u1, succ u2} β α (fun (x : α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) => u x))))
Case conversion may be inaccurate. Consider using '#align set.bInter_union Set.binterᵢ_unionₓ'. -/
theorem binterᵢ_union (s t : Set α) (u : α → Set β) :
    (⋂ x ∈ s ∪ t, u x) = (⋂ x ∈ s, u x) ∩ ⋂ x ∈ t, u x :=
  infᵢ_union
#align set.bInter_union Set.binterᵢ_union

/- warning: set.bInter_insert -> Set.binterᵢ_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (a : α) (s : Set.{u1} α) (t : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) => t x))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (t a) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => t x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (a : α) (s : Set.{u2} α) (t : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.interᵢ.{u1, succ u2} β α (fun (x : α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) a s)) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) a s)) => t x))) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (t a) (Set.interᵢ.{u1, succ u2} β α (fun (x : α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => t x))))
Case conversion may be inaccurate. Consider using '#align set.bInter_insert Set.binterᵢ_insertₓ'. -/
theorem binterᵢ_insert (a : α) (s : Set α) (t : α → Set β) :
    (⋂ x ∈ insert a s, t x) = t a ∩ ⋂ x ∈ s, t x := by simp
#align set.bInter_insert Set.binterᵢ_insert

/- warning: set.bInter_pair -> Set.binterᵢ_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (a : α) (b : α) (s : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b))) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b))) => s x))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (s a) (s b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (a : α) (b : α) (s : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b))) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b))) => s x))) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (s a) (s b))
Case conversion may be inaccurate. Consider using '#align set.bInter_pair Set.binterᵢ_pairₓ'. -/
-- TODO(Jeremy): another example of where an annotation is needed
theorem binterᵢ_pair (a b : α) (s : α → Set β) : (⋂ x ∈ ({a, b} : Set α), s x) = s a ∩ s b := by
  rw [bInter_insert, bInter_singleton]
#align set.bInter_pair Set.binterᵢ_pair

/- warning: set.bInter_inter -> Set.binterᵢ_inter is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {s : Set.{u1} ι}, (Set.Nonempty.{u1} ι s) -> (forall (f : ι -> (Set.{u2} α)) (t : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.interᵢ.{u2, 0} α (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => Inter.inter.{u2} (Set.{u2} α) (Set.hasInter.{u2} α) (f i) t))) (Inter.inter.{u2} (Set.{u2} α) (Set.hasInter.{u2} α) (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.interᵢ.{u2, 0} α (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => f i))) t))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {s : Set.{u2} ι}, (Set.Nonempty.{u2} ι s) -> (forall (f : ι -> (Set.{u1} α)) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (f i) t))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i))) t))
Case conversion may be inaccurate. Consider using '#align set.bInter_inter Set.binterᵢ_interₓ'. -/
theorem binterᵢ_inter {ι α : Type _} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    (⋂ i ∈ s, f i ∩ t) = (⋂ i ∈ s, f i) ∩ t :=
  by
  haveI : Nonempty s := hs.to_subtype
  simp [bInter_eq_Inter, ← Inter_inter]
#align set.bInter_inter Set.binterᵢ_inter

/- warning: set.inter_bInter -> Set.inter_binterᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {s : Set.{u1} ι}, (Set.Nonempty.{u1} ι s) -> (forall (f : ι -> (Set.{u2} α)) (t : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.interᵢ.{u2, 0} α (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => Inter.inter.{u2} (Set.{u2} α) (Set.hasInter.{u2} α) t (f i)))) (Inter.inter.{u2} (Set.{u2} α) (Set.hasInter.{u2} α) t (Set.interᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.interᵢ.{u2, 0} α (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => f i)))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {s : Set.{u2} ι}, (Set.Nonempty.{u2} ι s) -> (forall (f : ι -> (Set.{u1} α)) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t (f i)))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t (Set.interᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i)))))
Case conversion may be inaccurate. Consider using '#align set.inter_bInter Set.inter_binterᵢₓ'. -/
theorem inter_binterᵢ {ι α : Type _} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    (⋂ i ∈ s, t ∩ f i) = t ∩ ⋂ i ∈ s, f i :=
  by
  rw [inter_comm, ← bInter_inter hs]
  simp [inter_comm]
#align set.inter_bInter Set.inter_binterᵢ

#print Set.bunionᵢ_empty /-
theorem bunionᵢ_empty (s : α → Set β) : (⋃ x ∈ (∅ : Set α), s x) = ∅ :=
  supᵢ_emptyset
#align set.bUnion_empty Set.bunionᵢ_empty
-/

#print Set.bunionᵢ_univ /-
theorem bunionᵢ_univ (s : α → Set β) : (⋃ x ∈ @univ α, s x) = ⋃ x, s x :=
  supᵢ_univ
#align set.bUnion_univ Set.bunionᵢ_univ
-/

#print Set.bunionᵢ_singleton /-
theorem bunionᵢ_singleton (a : α) (s : α → Set β) : (⋃ x ∈ ({a} : Set α), s x) = s a :=
  supᵢ_singleton
#align set.bUnion_singleton Set.bunionᵢ_singleton
-/

#print Set.bunionᵢ_of_singleton /-
@[simp]
theorem bunionᵢ_of_singleton (s : Set α) : (⋃ x ∈ s, {x}) = s :=
  ext <| by simp
#align set.bUnion_of_singleton Set.bunionᵢ_of_singleton
-/

/- warning: set.bUnion_union -> Set.bunionᵢ_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : Set.{u1} α) (u : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) => u x))) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => u x))) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) => u x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : Set.{u2} α) (u : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) => u x))) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => u x))) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) => u x))))
Case conversion may be inaccurate. Consider using '#align set.bUnion_union Set.bunionᵢ_unionₓ'. -/
theorem bunionᵢ_union (s t : Set α) (u : α → Set β) :
    (⋃ x ∈ s ∪ t, u x) = (⋃ x ∈ s, u x) ∪ ⋃ x ∈ t, u x :=
  supᵢ_union
#align set.bUnion_union Set.bunionᵢ_union

/- warning: set.Union_coe_set -> Set.unionᵢ_coe_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (f : (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (fun (i : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => f i)) (Set.unionᵢ.{u2, succ u1} β α (fun (i : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) i H))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (f : (Set.Elem.{u2} α s) -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, succ u2} β (Set.Elem.{u2} α s) (fun (i : Set.Elem.{u2} α s) => f i)) (Set.unionᵢ.{u1, succ u2} β α (fun (i : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) i H))))
Case conversion may be inaccurate. Consider using '#align set.Union_coe_set Set.unionᵢ_coe_setₓ'. -/
@[simp]
theorem unionᵢ_coe_set {α β : Type _} (s : Set α) (f : s → Set β) :
    (⋃ i, f i) = ⋃ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  unionᵢ_subtype _ _
#align set.Union_coe_set Set.unionᵢ_coe_set

/- warning: set.Inter_coe_set -> Set.interᵢ_coe_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (f : (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, succ u1} β (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (fun (i : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => f i)) (Set.interᵢ.{u2, succ u1} β α (fun (i : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) i H))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (f : (Set.Elem.{u2} α s) -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.interᵢ.{u1, succ u2} β (Set.Elem.{u2} α s) (fun (i : Set.Elem.{u2} α s) => f i)) (Set.interᵢ.{u1, succ u2} β α (fun (i : α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) i H))))
Case conversion may be inaccurate. Consider using '#align set.Inter_coe_set Set.interᵢ_coe_setₓ'. -/
@[simp]
theorem interᵢ_coe_set {α β : Type _} (s : Set α) (f : s → Set β) :
    (⋂ i, f i) = ⋂ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  interᵢ_subtype _ _
#align set.Inter_coe_set Set.interᵢ_coe_set

/- warning: set.bUnion_insert -> Set.bunionᵢ_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (a : α) (s : Set.{u1} α) (t : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) => t x))) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (t a) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => t x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (a : α) (s : Set.{u2} α) (t : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) a s)) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) a s)) => t x))) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) (t a) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => t x))))
Case conversion may be inaccurate. Consider using '#align set.bUnion_insert Set.bunionᵢ_insertₓ'. -/
theorem bunionᵢ_insert (a : α) (s : Set α) (t : α → Set β) :
    (⋃ x ∈ insert a s, t x) = t a ∪ ⋃ x ∈ s, t x := by simp
#align set.bUnion_insert Set.bunionᵢ_insert

/- warning: set.bUnion_pair -> Set.bunionᵢ_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (a : α) (b : α) (s : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b))) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b))) => s x))) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (s a) (s b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (a : α) (b : α) (s : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b))) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b))) => s x))) (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) (s a) (s b))
Case conversion may be inaccurate. Consider using '#align set.bUnion_pair Set.bunionᵢ_pairₓ'. -/
theorem bunionᵢ_pair (a b : α) (s : α → Set β) : (⋃ x ∈ ({a, b} : Set α), s x) = s a ∪ s b := by
  simp
#align set.bUnion_pair Set.bunionᵢ_pair

/- warning: set.inter_Union₂ -> Set.inter_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} (s : Set.{u1} α) (t : forall (i : ι), (κ i) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => t i j)))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (t i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} (s : Set.{u3} α) (t : forall (i : ι), (κ i) -> (Set.{u3} α)), Eq.{succ u3} (Set.{u3} α) (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) s (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => t i j)))) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) s (t i j))))
Case conversion may be inaccurate. Consider using '#align set.inter_Union₂ Set.inter_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem inter_unionᵢ₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∩ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ∩ t i j := by simp only [inter_Union]
#align set.inter_Union₂ Set.inter_unionᵢ₂

/- warning: set.Union₂_inter -> Set.unionᵢ₂_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} (s : forall (i : ι), (κ i) -> (Set.{u1} α)) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) t) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (s i j) t)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} (s : forall (i : ι), (κ i) -> (Set.{u3} α)) (t : Set.{u3} α), Eq.{succ u3} (Set.{u3} α) (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) t) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) (s i j) t)))
Case conversion may be inaccurate. Consider using '#align set.Union₂_inter Set.unionᵢ₂_interₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem unionᵢ₂_inter (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) ∩ t = ⋃ (i) (j), s i j ∩ t := by simp_rw [Union_inter]
#align set.Union₂_inter Set.unionᵢ₂_inter

/- warning: set.union_Inter₂ -> Set.union_interᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} (s : Set.{u1} α) (t : forall (i : ι), (κ i) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (t i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} (s : Set.{u3} α) (t : forall (i : ι), (κ i) -> (Set.{u3} α)), Eq.{succ u3} (Set.{u3} α) (Union.union.{u3} (Set.{u3} α) (Set.instUnionSet.{u3} α) s (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => Union.union.{u3} (Set.{u3} α) (Set.instUnionSet.{u3} α) s (t i j))))
Case conversion may be inaccurate. Consider using '#align set.union_Inter₂ Set.union_interᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem union_interᵢ₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j := by simp_rw [union_Inter]
#align set.union_Inter₂ Set.union_interᵢ₂

/- warning: set.Inter₂_union -> Set.interᵢ₂_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} (s : forall (i : ι), (κ i) -> (Set.{u1} α)) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) t) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (s i j) t)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} (s : forall (i : ι), (κ i) -> (Set.{u3} α)) (t : Set.{u3} α), Eq.{succ u3} (Set.{u3} α) (Union.union.{u3} (Set.{u3} α) (Set.instUnionSet.{u3} α) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) t) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => Union.union.{u3} (Set.{u3} α) (Set.instUnionSet.{u3} α) (s i j) t)))
Case conversion may be inaccurate. Consider using '#align set.Inter₂_union Set.interᵢ₂_unionₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem interᵢ₂_union (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t := by simp_rw [Inter_union]
#align set.Inter₂_union Set.interᵢ₂_union

#print Set.mem_unionₛ_of_mem /-
theorem mem_unionₛ_of_mem {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∈ t) (ht : t ∈ S) :
    x ∈ ⋃₀ S :=
  ⟨t, ht, hx⟩
#align set.mem_sUnion_of_mem Set.mem_unionₛ_of_mem
-/

#print Set.not_mem_of_not_mem_unionₛ /-
-- is this theorem really necessary?
theorem not_mem_of_not_mem_unionₛ {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∉ ⋃₀ S)
    (ht : t ∈ S) : x ∉ t := fun h => hx ⟨t, ht, h⟩
#align set.not_mem_of_not_mem_sUnion Set.not_mem_of_not_mem_unionₛ
-/

#print Set.interₛ_subset_of_mem /-
theorem interₛ_subset_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : ⋂₀ S ⊆ t :=
  infₛ_le tS
#align set.sInter_subset_of_mem Set.interₛ_subset_of_mem
-/

#print Set.subset_unionₛ_of_mem /-
theorem subset_unionₛ_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : t ⊆ ⋃₀ S :=
  le_supₛ tS
#align set.subset_sUnion_of_mem Set.subset_unionₛ_of_mem
-/

#print Set.subset_unionₛ_of_subset /-
theorem subset_unionₛ_of_subset {s : Set α} (t : Set (Set α)) (u : Set α) (h₁ : s ⊆ u)
    (h₂ : u ∈ t) : s ⊆ ⋃₀ t :=
  Subset.trans h₁ (subset_unionₛ_of_mem h₂)
#align set.subset_sUnion_of_subset Set.subset_unionₛ_of_subset
-/

#print Set.unionₛ_subset /-
theorem unionₛ_subset {S : Set (Set α)} {t : Set α} (h : ∀ t' ∈ S, t' ⊆ t) : ⋃₀ S ⊆ t :=
  supₛ_le h
#align set.sUnion_subset Set.unionₛ_subset
-/

#print Set.unionₛ_subset_iff /-
@[simp]
theorem unionₛ_subset_iff {s : Set (Set α)} {t : Set α} : ⋃₀ s ⊆ t ↔ ∀ t' ∈ s, t' ⊆ t :=
  @supₛ_le_iff (Set α) _ _ _
#align set.sUnion_subset_iff Set.unionₛ_subset_iff
-/

#print Set.subset_interₛ /-
theorem subset_interₛ {S : Set (Set α)} {t : Set α} (h : ∀ t' ∈ S, t ⊆ t') : t ⊆ ⋂₀ S :=
  le_infₛ h
#align set.subset_sInter Set.subset_interₛ
-/

#print Set.subset_interₛ_iff /-
@[simp]
theorem subset_interₛ_iff {S : Set (Set α)} {t : Set α} : t ⊆ ⋂₀ S ↔ ∀ t' ∈ S, t ⊆ t' :=
  @le_infₛ_iff (Set α) _ _ _
#align set.subset_sInter_iff Set.subset_interₛ_iff
-/

#print Set.unionₛ_subset_unionₛ /-
theorem unionₛ_subset_unionₛ {S T : Set (Set α)} (h : S ⊆ T) : ⋃₀ S ⊆ ⋃₀ T :=
  sUnion_subset fun s hs => subset_unionₛ_of_mem (h hs)
#align set.sUnion_subset_sUnion Set.unionₛ_subset_unionₛ
-/

#print Set.interₛ_subset_interₛ /-
theorem interₛ_subset_interₛ {S T : Set (Set α)} (h : S ⊆ T) : ⋂₀ T ⊆ ⋂₀ S :=
  subset_sInter fun s hs => interₛ_subset_of_mem (h hs)
#align set.sInter_subset_sInter Set.interₛ_subset_interₛ
-/

#print Set.unionₛ_empty /-
@[simp]
theorem unionₛ_empty : ⋃₀ ∅ = (∅ : Set α) :=
  supₛ_empty
#align set.sUnion_empty Set.unionₛ_empty
-/

#print Set.interₛ_empty /-
@[simp]
theorem interₛ_empty : ⋂₀ ∅ = (univ : Set α) :=
  infₛ_empty
#align set.sInter_empty Set.interₛ_empty
-/

#print Set.unionₛ_singleton /-
@[simp]
theorem unionₛ_singleton (s : Set α) : ⋃₀ {s} = s :=
  supₛ_singleton
#align set.sUnion_singleton Set.unionₛ_singleton
-/

#print Set.interₛ_singleton /-
@[simp]
theorem interₛ_singleton (s : Set α) : ⋂₀ {s} = s :=
  infₛ_singleton
#align set.sInter_singleton Set.interₛ_singleton
-/

#print Set.unionₛ_eq_empty /-
@[simp]
theorem unionₛ_eq_empty {S : Set (Set α)} : ⋃₀ S = ∅ ↔ ∀ s ∈ S, s = ∅ :=
  supₛ_eq_bot
#align set.sUnion_eq_empty Set.unionₛ_eq_empty
-/

#print Set.interₛ_eq_univ /-
@[simp]
theorem interₛ_eq_univ {S : Set (Set α)} : ⋂₀ S = univ ↔ ∀ s ∈ S, s = univ :=
  infₛ_eq_top
#align set.sInter_eq_univ Set.interₛ_eq_univ
-/

/- warning: set.nonempty_sUnion -> Set.nonempty_unionₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {S : Set.{u1} (Set.{u1} α)}, Iff (Set.Nonempty.{u1} α (Set.unionₛ.{u1} α S)) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s S) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s S) => Set.Nonempty.{u1} α s)))
but is expected to have type
  forall {α : Type.{u1}} {S : Set.{u1} (Set.{u1} α)}, Iff (Set.Nonempty.{u1} α (Set.unionₛ.{u1} α S)) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s S) (Set.Nonempty.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align set.nonempty_sUnion Set.nonempty_unionₛₓ'. -/
@[simp]
theorem nonempty_unionₛ {S : Set (Set α)} : (⋃₀ S).Nonempty ↔ ∃ s ∈ S, Set.Nonempty s := by
  simp [nonempty_iff_ne_empty]
#align set.nonempty_sUnion Set.nonempty_unionₛ

#print Set.Nonempty.of_unionₛ /-
theorem Nonempty.of_unionₛ {s : Set (Set α)} (h : (⋃₀ s).Nonempty) : s.Nonempty :=
  let ⟨s, hs, _⟩ := nonempty_unionₛ.1 h
  ⟨s, hs⟩
#align set.nonempty.of_sUnion Set.Nonempty.of_unionₛ
-/

#print Set.Nonempty.of_unionₛ_eq_univ /-
theorem Nonempty.of_unionₛ_eq_univ [Nonempty α] {s : Set (Set α)} (h : ⋃₀ s = univ) : s.Nonempty :=
  nonempty.of_sUnion <| h.symm ▸ univ_nonempty
#align set.nonempty.of_sUnion_eq_univ Set.Nonempty.of_unionₛ_eq_univ
-/

/- warning: set.sUnion_union -> Set.unionₛ_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)) (T : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α (Union.union.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasUnion.{u1} (Set.{u1} α)) S T)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Set.unionₛ.{u1} α S) (Set.unionₛ.{u1} α T))
but is expected to have type
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)) (T : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α (Union.union.{u1} (Set.{u1} (Set.{u1} α)) (Set.instUnionSet.{u1} (Set.{u1} α)) S T)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Set.unionₛ.{u1} α S) (Set.unionₛ.{u1} α T))
Case conversion may be inaccurate. Consider using '#align set.sUnion_union Set.unionₛ_unionₓ'. -/
theorem unionₛ_union (S T : Set (Set α)) : ⋃₀ (S ∪ T) = ⋃₀ S ∪ ⋃₀ T :=
  supₛ_union
#align set.sUnion_union Set.unionₛ_union

/- warning: set.sInter_union -> Set.interₛ_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)) (T : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interₛ.{u1} α (Union.union.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasUnion.{u1} (Set.{u1} α)) S T)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.interₛ.{u1} α S) (Set.interₛ.{u1} α T))
but is expected to have type
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)) (T : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interₛ.{u1} α (Union.union.{u1} (Set.{u1} (Set.{u1} α)) (Set.instUnionSet.{u1} (Set.{u1} α)) S T)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.interₛ.{u1} α S) (Set.interₛ.{u1} α T))
Case conversion may be inaccurate. Consider using '#align set.sInter_union Set.interₛ_unionₓ'. -/
theorem interₛ_union (S T : Set (Set α)) : ⋂₀ (S ∪ T) = ⋂₀ S ∩ ⋂₀ T :=
  infₛ_union
#align set.sInter_union Set.interₛ_union

/- warning: set.sUnion_insert -> Set.unionₛ_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (T : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasInsert.{u1} (Set.{u1} α)) s T)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (Set.unionₛ.{u1} α T))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (T : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instInsertSet.{u1} (Set.{u1} α)) s T)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s (Set.unionₛ.{u1} α T))
Case conversion may be inaccurate. Consider using '#align set.sUnion_insert Set.unionₛ_insertₓ'. -/
@[simp]
theorem unionₛ_insert (s : Set α) (T : Set (Set α)) : ⋃₀ insert s T = s ∪ ⋃₀ T :=
  supₛ_insert
#align set.sUnion_insert Set.unionₛ_insert

/- warning: set.sInter_insert -> Set.interₛ_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (T : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interₛ.{u1} α (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasInsert.{u1} (Set.{u1} α)) s T)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.interₛ.{u1} α T))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (T : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interₛ.{u1} α (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instInsertSet.{u1} (Set.{u1} α)) s T)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Set.interₛ.{u1} α T))
Case conversion may be inaccurate. Consider using '#align set.sInter_insert Set.interₛ_insertₓ'. -/
@[simp]
theorem interₛ_insert (s : Set α) (T : Set (Set α)) : ⋂₀ insert s T = s ∩ ⋂₀ T :=
  infₛ_insert
#align set.sInter_insert Set.interₛ_insert

/- warning: set.sUnion_diff_singleton_empty -> Set.unionₛ_diff_singleton_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α (SDiff.sdiff.{u1} (Set.{u1} (Set.{u1} α)) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} (Set.{u1} α)) (Set.booleanAlgebra.{u1} (Set.{u1} α))) s (Singleton.singleton.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasSingleton.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))))) (Set.unionₛ.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α (SDiff.sdiff.{u1} (Set.{u1} (Set.{u1} α)) (Set.instSDiffSet.{u1} (Set.{u1} α)) s (Singleton.singleton.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instSingletonSet.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))))) (Set.unionₛ.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.sUnion_diff_singleton_empty Set.unionₛ_diff_singleton_emptyₓ'. -/
@[simp]
theorem unionₛ_diff_singleton_empty (s : Set (Set α)) : ⋃₀ (s \ {∅}) = ⋃₀ s :=
  supₛ_diff_singleton_bot s
#align set.sUnion_diff_singleton_empty Set.unionₛ_diff_singleton_empty

/- warning: set.sInter_diff_singleton_univ -> Set.interₛ_diff_singleton_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interₛ.{u1} α (SDiff.sdiff.{u1} (Set.{u1} (Set.{u1} α)) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} (Set.{u1} α)) (Set.booleanAlgebra.{u1} (Set.{u1} α))) s (Singleton.singleton.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasSingleton.{u1} (Set.{u1} α)) (Set.univ.{u1} α)))) (Set.interₛ.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interₛ.{u1} α (SDiff.sdiff.{u1} (Set.{u1} (Set.{u1} α)) (Set.instSDiffSet.{u1} (Set.{u1} α)) s (Singleton.singleton.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instSingletonSet.{u1} (Set.{u1} α)) (Set.univ.{u1} α)))) (Set.interₛ.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.sInter_diff_singleton_univ Set.interₛ_diff_singleton_univₓ'. -/
@[simp]
theorem interₛ_diff_singleton_univ (s : Set (Set α)) : ⋂₀ (s \ {univ}) = ⋂₀ s :=
  infₛ_diff_singleton_top s
#align set.sInter_diff_singleton_univ Set.interₛ_diff_singleton_univ

/- warning: set.sUnion_pair -> Set.unionₛ_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasInsert.{u1} (Set.{u1} α)) s (Singleton.singleton.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasSingleton.{u1} (Set.{u1} α)) t))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instInsertSet.{u1} (Set.{u1} α)) s (Singleton.singleton.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instSingletonSet.{u1} (Set.{u1} α)) t))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.sUnion_pair Set.unionₛ_pairₓ'. -/
theorem unionₛ_pair (s t : Set α) : ⋃₀ {s, t} = s ∪ t :=
  supₛ_pair
#align set.sUnion_pair Set.unionₛ_pair

/- warning: set.sInter_pair -> Set.interₛ_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.interₛ.{u1} α (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasInsert.{u1} (Set.{u1} α)) s (Singleton.singleton.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasSingleton.{u1} (Set.{u1} α)) t))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.interₛ.{u1} α (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instInsertSet.{u1} (Set.{u1} α)) s (Singleton.singleton.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instSingletonSet.{u1} (Set.{u1} α)) t))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.sInter_pair Set.interₛ_pairₓ'. -/
theorem interₛ_pair (s t : Set α) : ⋂₀ {s, t} = s ∩ t :=
  infₛ_pair
#align set.sInter_pair Set.interₛ_pair

#print Set.unionₛ_image /-
@[simp]
theorem unionₛ_image (f : α → Set β) (s : Set α) : ⋃₀ (f '' s) = ⋃ x ∈ s, f x :=
  supₛ_image
#align set.sUnion_image Set.unionₛ_image
-/

#print Set.interₛ_image /-
@[simp]
theorem interₛ_image (f : α → Set β) (s : Set α) : ⋂₀ (f '' s) = ⋂ x ∈ s, f x :=
  infₛ_image
#align set.sInter_image Set.interₛ_image
-/

/- warning: set.sUnion_range -> Set.unionₛ_range is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.unionₛ.{u1} β (Set.range.{u1, u2} (Set.{u1} β) ι f)) (Set.unionᵢ.{u1, u2} β ι (fun (x : ι) => f x))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (f : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.unionₛ.{u2} β (Set.range.{u2, u1} (Set.{u2} β) ι f)) (Set.unionᵢ.{u2, u1} β ι (fun (x : ι) => f x))
Case conversion may be inaccurate. Consider using '#align set.sUnion_range Set.unionₛ_rangeₓ'. -/
@[simp]
theorem unionₛ_range (f : ι → Set β) : ⋃₀ range f = ⋃ x, f x :=
  rfl
#align set.sUnion_range Set.unionₛ_range

/- warning: set.sInter_range -> Set.interₛ_range is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.interₛ.{u1} β (Set.range.{u1, u2} (Set.{u1} β) ι f)) (Set.interᵢ.{u1, u2} β ι (fun (x : ι) => f x))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (f : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.interₛ.{u2} β (Set.range.{u2, u1} (Set.{u2} β) ι f)) (Set.interᵢ.{u2, u1} β ι (fun (x : ι) => f x))
Case conversion may be inaccurate. Consider using '#align set.sInter_range Set.interₛ_rangeₓ'. -/
@[simp]
theorem interₛ_range (f : ι → Set β) : ⋂₀ range f = ⋂ x, f x :=
  rfl
#align set.sInter_range Set.interₛ_range

/- warning: set.Union_eq_univ_iff -> Set.unionᵢ_eq_univ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Set.{u1} α)}, Iff (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => f i)) (Set.univ.{u1} α)) (forall (x : α), Exists.{u2} ι (fun (i : ι) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> (Set.{u2} α)}, Iff (Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => f i)) (Set.univ.{u2} α)) (forall (x : α), Exists.{u1} ι (fun (i : ι) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (f i)))
Case conversion may be inaccurate. Consider using '#align set.Union_eq_univ_iff Set.unionᵢ_eq_univ_iffₓ'. -/
theorem unionᵢ_eq_univ_iff {f : ι → Set α} : (⋃ i, f i) = univ ↔ ∀ x, ∃ i, x ∈ f i := by
  simp only [eq_univ_iff_forall, mem_Union]
#align set.Union_eq_univ_iff Set.unionᵢ_eq_univ_iff

/- warning: set.Union₂_eq_univ_iff -> Set.unionᵢ₂_eq_univ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)}, Iff (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) (Set.univ.{u1} α)) (forall (a : α), Exists.{u2} ι (fun (i : ι) => Exists.{u3} (κ i) (fun (j : κ i) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (s i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u3} α)}, Iff (Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) (Set.univ.{u3} α)) (forall (a : α), Exists.{u2} ι (fun (i : ι) => Exists.{u1} (κ i) (fun (j : κ i) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (s i j))))
Case conversion may be inaccurate. Consider using '#align set.Union₂_eq_univ_iff Set.unionᵢ₂_eq_univ_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem unionᵢ₂_eq_univ_iff {s : ∀ i, κ i → Set α} :
    (⋃ (i) (j), s i j) = univ ↔ ∀ a, ∃ i j, a ∈ s i j := by simp only [Union_eq_univ_iff, mem_Union]
#align set.Union₂_eq_univ_iff Set.unionᵢ₂_eq_univ_iff

/- warning: set.sUnion_eq_univ_iff -> Set.unionₛ_eq_univ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {c : Set.{u1} (Set.{u1} α)}, Iff (Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α c) (Set.univ.{u1} α)) (forall (a : α), Exists.{succ u1} (Set.{u1} α) (fun (b : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) b c) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) b c) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a b)))
but is expected to have type
  forall {α : Type.{u1}} {c : Set.{u1} (Set.{u1} α)}, Iff (Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α c) (Set.univ.{u1} α)) (forall (a : α), Exists.{succ u1} (Set.{u1} α) (fun (b : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) b c) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a b)))
Case conversion may be inaccurate. Consider using '#align set.sUnion_eq_univ_iff Set.unionₛ_eq_univ_iffₓ'. -/
theorem unionₛ_eq_univ_iff {c : Set (Set α)} : ⋃₀ c = univ ↔ ∀ a, ∃ b ∈ c, a ∈ b := by
  simp only [eq_univ_iff_forall, mem_sUnion]
#align set.sUnion_eq_univ_iff Set.unionₛ_eq_univ_iff

/- warning: set.Inter_eq_empty_iff -> Set.interᵢ_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Set.{u1} α)}, Iff (Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => f i)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (forall (x : α), Exists.{u2} ι (fun (i : ι) => Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> (Set.{u2} α)}, Iff (Eq.{succ u2} (Set.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => f i)) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (forall (x : α), Exists.{u1} ι (fun (i : ι) => Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (f i))))
Case conversion may be inaccurate. Consider using '#align set.Inter_eq_empty_iff Set.interᵢ_eq_empty_iffₓ'. -/
-- classical
theorem interᵢ_eq_empty_iff {f : ι → Set α} : (⋂ i, f i) = ∅ ↔ ∀ x, ∃ i, x ∉ f i := by
  simp [Set.eq_empty_iff_forall_not_mem]
#align set.Inter_eq_empty_iff Set.interᵢ_eq_empty_iff

/- warning: set.Inter₂_eq_empty_iff -> Set.interᵢ₂_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)}, Iff (Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (forall (a : α), Exists.{u2} ι (fun (i : ι) => Exists.{u3} (κ i) (fun (j : κ i) => Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (s i j)))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u3} α)}, Iff (Eq.{succ u3} (Set.{u3} α) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) (EmptyCollection.emptyCollection.{u3} (Set.{u3} α) (Set.instEmptyCollectionSet.{u3} α))) (forall (a : α), Exists.{u2} ι (fun (i : ι) => Exists.{u1} (κ i) (fun (j : κ i) => Not (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (s i j)))))
Case conversion may be inaccurate. Consider using '#align set.Inter₂_eq_empty_iff Set.interᵢ₂_eq_empty_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
-- classical
theorem interᵢ₂_eq_empty_iff {s : ∀ i, κ i → Set α} :
    (⋂ (i) (j), s i j) = ∅ ↔ ∀ a, ∃ i j, a ∉ s i j := by
  simp only [eq_empty_iff_forall_not_mem, mem_Inter, not_forall]
#align set.Inter₂_eq_empty_iff Set.interᵢ₂_eq_empty_iff

/- warning: set.sInter_eq_empty_iff -> Set.interₛ_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {c : Set.{u1} (Set.{u1} α)}, Iff (Eq.{succ u1} (Set.{u1} α) (Set.interₛ.{u1} α c) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (forall (a : α), Exists.{succ u1} (Set.{u1} α) (fun (b : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) b c) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) b c) => Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a b))))
but is expected to have type
  forall {α : Type.{u1}} {c : Set.{u1} (Set.{u1} α)}, Iff (Eq.{succ u1} (Set.{u1} α) (Set.interₛ.{u1} α c) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (forall (a : α), Exists.{succ u1} (Set.{u1} α) (fun (b : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) b c) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a b))))
Case conversion may be inaccurate. Consider using '#align set.sInter_eq_empty_iff Set.interₛ_eq_empty_iffₓ'. -/
-- classical
theorem interₛ_eq_empty_iff {c : Set (Set α)} : ⋂₀ c = ∅ ↔ ∀ a, ∃ b ∈ c, a ∉ b := by
  simp [Set.eq_empty_iff_forall_not_mem]
#align set.sInter_eq_empty_iff Set.interₛ_eq_empty_iff

/- warning: set.nonempty_Inter -> Set.nonempty_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Set.{u1} α)}, Iff (Set.Nonempty.{u1} α (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => f i))) (Exists.{succ u1} α (fun (x : α) => forall (i : ι), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> (Set.{u2} α)}, Iff (Set.Nonempty.{u2} α (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => f i))) (Exists.{succ u2} α (fun (x : α) => forall (i : ι), Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (f i)))
Case conversion may be inaccurate. Consider using '#align set.nonempty_Inter Set.nonempty_interᵢₓ'. -/
-- classical
@[simp]
theorem nonempty_interᵢ {f : ι → Set α} : (⋂ i, f i).Nonempty ↔ ∃ x, ∀ i, x ∈ f i := by
  simp [nonempty_iff_ne_empty, Inter_eq_empty_iff]
#align set.nonempty_Inter Set.nonempty_interᵢ

/- warning: set.nonempty_Inter₂ -> Set.nonempty_interᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)}, Iff (Set.Nonempty.{u1} α (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j)))) (Exists.{succ u1} α (fun (a : α) => forall (i : ι) (j : κ i), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (s i j)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u3} α)}, Iff (Set.Nonempty.{u3} α (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j)))) (Exists.{succ u3} α (fun (a : α) => forall (i : ι) (j : κ i), Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (s i j)))
Case conversion may be inaccurate. Consider using '#align set.nonempty_Inter₂ Set.nonempty_interᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
-- classical
@[simp]
theorem nonempty_interᵢ₂ {s : ∀ i, κ i → Set α} :
    (⋂ (i) (j), s i j).Nonempty ↔ ∃ a, ∀ i j, a ∈ s i j := by
  simp [nonempty_iff_ne_empty, Inter_eq_empty_iff]
#align set.nonempty_Inter₂ Set.nonempty_interᵢ₂

#print Set.nonempty_interₛ /-
-- classical
@[simp]
theorem nonempty_interₛ {c : Set (Set α)} : (⋂₀ c).Nonempty ↔ ∃ a, ∀ b ∈ c, a ∈ b := by
  simp [nonempty_iff_ne_empty, sInter_eq_empty_iff]
#align set.nonempty_sInter Set.nonempty_interₛ
-/

/- warning: set.compl_sUnion -> Set.compl_unionₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Set.unionₛ.{u1} α S)) (Set.interₛ.{u1} α (Set.image.{u1, u1} (Set.{u1} α) (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) S))
but is expected to have type
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Set.unionₛ.{u1} α S)) (Set.interₛ.{u1} α (Set.image.{u1, u1} (Set.{u1} α) (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) S))
Case conversion may be inaccurate. Consider using '#align set.compl_sUnion Set.compl_unionₛₓ'. -/
-- classical
theorem compl_unionₛ (S : Set (Set α)) : (⋃₀ S)ᶜ = ⋂₀ (compl '' S) :=
  ext fun x => by simp
#align set.compl_sUnion Set.compl_unionₛ

/- warning: set.sUnion_eq_compl_sInter_compl -> Set.unionₛ_eq_compl_interₛ_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α S) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Set.interₛ.{u1} α (Set.image.{u1, u1} (Set.{u1} α) (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) S)))
but is expected to have type
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α S) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Set.interₛ.{u1} α (Set.image.{u1, u1} (Set.{u1} α) (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) S)))
Case conversion may be inaccurate. Consider using '#align set.sUnion_eq_compl_sInter_compl Set.unionₛ_eq_compl_interₛ_complₓ'. -/
-- classical
theorem unionₛ_eq_compl_interₛ_compl (S : Set (Set α)) : ⋃₀ S = (⋂₀ (compl '' S))ᶜ := by
  rw [← compl_compl (⋃₀ S), compl_sUnion]
#align set.sUnion_eq_compl_sInter_compl Set.unionₛ_eq_compl_interₛ_compl

/- warning: set.compl_sInter -> Set.compl_interₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Set.interₛ.{u1} α S)) (Set.unionₛ.{u1} α (Set.image.{u1, u1} (Set.{u1} α) (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) S))
but is expected to have type
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Set.interₛ.{u1} α S)) (Set.unionₛ.{u1} α (Set.image.{u1, u1} (Set.{u1} α) (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) S))
Case conversion may be inaccurate. Consider using '#align set.compl_sInter Set.compl_interₛₓ'. -/
-- classical
theorem compl_interₛ (S : Set (Set α)) : (⋂₀ S)ᶜ = ⋃₀ (compl '' S) := by
  rw [sUnion_eq_compl_sInter_compl, compl_compl_image]
#align set.compl_sInter Set.compl_interₛ

/- warning: set.sInter_eq_compl_sUnion_compl -> Set.interₛ_eq_compl_unionₛ_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interₛ.{u1} α S) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Set.unionₛ.{u1} α (Set.image.{u1, u1} (Set.{u1} α) (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) S)))
but is expected to have type
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interₛ.{u1} α S) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Set.unionₛ.{u1} α (Set.image.{u1, u1} (Set.{u1} α) (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) S)))
Case conversion may be inaccurate. Consider using '#align set.sInter_eq_compl_sUnion_compl Set.interₛ_eq_compl_unionₛ_complₓ'. -/
-- classical
theorem interₛ_eq_compl_unionₛ_compl (S : Set (Set α)) : ⋂₀ S = (⋃₀ (compl '' S))ᶜ := by
  rw [← compl_compl (⋂₀ S), compl_sInter]
#align set.sInter_eq_compl_sUnion_compl Set.interₛ_eq_compl_unionₛ_compl

/- warning: set.inter_empty_of_inter_sUnion_empty -> Set.inter_empty_of_inter_unionₛ_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {S : Set.{u1} (Set.{u1} α)}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t S) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.unionₛ.{u1} α S)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {S : Set.{u1} (Set.{u1} α)}, (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) t S) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Set.unionₛ.{u1} α S)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align set.inter_empty_of_inter_sUnion_empty Set.inter_empty_of_inter_unionₛ_emptyₓ'. -/
theorem inter_empty_of_inter_unionₛ_empty {s t : Set α} {S : Set (Set α)} (hs : t ∈ S)
    (h : s ∩ ⋃₀ S = ∅) : s ∩ t = ∅ :=
  eq_empty_of_subset_empty <| by
    rw [← h] <;> exact inter_subset_inter_right _ (subset_sUnion_of_mem hs)
#align set.inter_empty_of_inter_sUnion_empty Set.inter_empty_of_inter_unionₛ_empty

/- warning: set.range_sigma_eq_Union_range -> Set.range_sigma_eq_unionᵢ_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : α -> Type.{u3}} (f : (Sigma.{u1, u3} α γ) -> β), Eq.{succ u2} (Set.{u2} β) (Set.range.{u2, max (succ u1) (succ u3)} β (Sigma.{u1, u3} α γ) f) (Set.unionᵢ.{u2, succ u1} β α (fun (a : α) => Set.range.{u2, succ u3} β (γ a) (fun (b : γ a) => f (Sigma.mk.{u1, u3} α γ a b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : α -> Type.{u3}} (f : (Sigma.{u2, u3} α γ) -> β), Eq.{succ u1} (Set.{u1} β) (Set.range.{u1, max (succ u2) (succ u3)} β (Sigma.{u2, u3} α γ) f) (Set.unionᵢ.{u1, succ u2} β α (fun (a : α) => Set.range.{u1, succ u3} β (γ a) (fun (b : γ a) => f (Sigma.mk.{u2, u3} α γ a b))))
Case conversion may be inaccurate. Consider using '#align set.range_sigma_eq_Union_range Set.range_sigma_eq_unionᵢ_rangeₓ'. -/
theorem range_sigma_eq_unionᵢ_range {γ : α → Type _} (f : Sigma γ → β) :
    range f = ⋃ a, range fun b => f ⟨a, b⟩ :=
  Set.ext <| by simp
#align set.range_sigma_eq_Union_range Set.range_sigma_eq_unionᵢ_range

#print Set.unionᵢ_eq_range_sigma /-
theorem unionᵢ_eq_range_sigma (s : α → Set β) : (⋃ i, s i) = range fun a : Σi, s i => a.2 := by
  simp [Set.ext_iff]
#align set.Union_eq_range_sigma Set.unionᵢ_eq_range_sigma
-/

/- warning: set.Union_eq_range_psigma -> Set.unionᵢ_eq_range_psigma is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => s i)) (Set.range.{u1, max 1 u2 (succ u1)} β (PSigma.{u2, succ u1} ι (fun (i : ι) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (s i))) (fun (a : PSigma.{u2, succ u1} ι (fun (i : ι) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (s i))) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (s (PSigma.fst.{u2, succ u1} ι (fun (i : ι) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (s i)) a))) β (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (s (PSigma.fst.{u2, succ u1} ι (fun (i : ι) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (s i)) a))) β (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (s (PSigma.fst.{u2, succ u1} ι (fun (i : ι) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (s i)) a))) β (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (s (PSigma.fst.{u2, succ u1} ι (fun (i : ι) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (s i)) a))) β (coeSubtype.{succ u1} β (fun (x : β) => Membership.Mem.{u1, u1} β (Set.{u1} β) (Set.hasMem.{u1} β) x (s (PSigma.fst.{u2, succ u1} ι (fun (i : ι) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (s i)) a))))))) (PSigma.snd.{u2, succ u1} ι (fun (i : ι) => coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (s i)) a)))
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => s i)) (Set.range.{u2, max (succ u2) u1} β (PSigma.{u1, succ u2} ι (fun (i : ι) => Set.Elem.{u2} β (s i))) (fun (a : PSigma.{u1, succ u2} ι (fun (i : ι) => Set.Elem.{u2} β (s i))) => Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (s (PSigma.fst.{u1, succ u2} ι (fun (i : ι) => Set.Elem.{u2} β (s i)) a))) (PSigma.snd.{u1, succ u2} ι (fun (i : ι) => Set.Elem.{u2} β (s i)) a)))
Case conversion may be inaccurate. Consider using '#align set.Union_eq_range_psigma Set.unionᵢ_eq_range_psigmaₓ'. -/
theorem unionᵢ_eq_range_psigma (s : ι → Set β) : (⋃ i, s i) = range fun a : Σ'i, s i => a.2 := by
  simp [Set.ext_iff]
#align set.Union_eq_range_psigma Set.unionᵢ_eq_range_psigma

/- warning: set.Union_image_preimage_sigma_mk_eq_self -> Set.unionᵢ_image_preimage_sigma_mk_eq_self is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} (s : Set.{max u1 u2} (Sigma.{u1, u2} ι σ)), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι σ)) (Set.unionᵢ.{max u1 u2, succ u1} (Sigma.{u1, u2} ι σ) ι (fun (i : ι) => Set.image.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (Sigma.mk.{u1, u2} ι σ i) (Set.preimage.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (Sigma.mk.{u1, u2} ι σ i) s))) s
but is expected to have type
  forall {ι : Type.{u2}} {σ : ι -> Type.{u1}} (s : Set.{max u1 u2} (Sigma.{u2, u1} ι σ)), Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => σ i))) (Set.unionᵢ.{max u1 u2, succ u2} (Sigma.{u2, u1} ι (fun (i : ι) => σ i)) ι (fun (i : ι) => Set.image.{u1, max u1 u2} (σ i) (Sigma.{u2, u1} ι (fun (i : ι) => σ i)) (Sigma.mk.{u2, u1} ι (fun (i : ι) => σ i) i) (Set.preimage.{u1, max u2 u1} (σ i) (Sigma.{u2, u1} ι σ) (Sigma.mk.{u2, u1} ι σ i) s))) s
Case conversion may be inaccurate. Consider using '#align set.Union_image_preimage_sigma_mk_eq_self Set.unionᵢ_image_preimage_sigma_mk_eq_selfₓ'. -/
theorem unionᵢ_image_preimage_sigma_mk_eq_self {ι : Type _} {σ : ι → Type _} (s : Set (Sigma σ)) :
    (⋃ i, Sigma.mk i '' (Sigma.mk i ⁻¹' s)) = s :=
  by
  ext x
  simp only [mem_Union, mem_image, mem_preimage]
  constructor
  · rintro ⟨i, a, h, rfl⟩
    exact h
  · intro h
    cases' x with i a
    exact ⟨i, a, h, rfl⟩
#align set.Union_image_preimage_sigma_mk_eq_self Set.unionᵢ_image_preimage_sigma_mk_eq_self

#print Set.Sigma.univ /-
theorem Sigma.univ (X : α → Type _) : (Set.univ : Set (Σa, X a)) = ⋃ a, range (Sigma.mk a) :=
  Set.ext fun x =>
    iff_of_true trivial ⟨range (Sigma.mk x.1), Set.mem_range_self _, x.2, Sigma.eta x⟩
#align set.sigma.univ Set.Sigma.univ
-/

#print Set.unionₛ_mono /-
theorem unionₛ_mono {s t : Set (Set α)} (h : s ⊆ t) : ⋃₀ s ⊆ ⋃₀ t :=
  sUnion_subset fun t' ht' => subset_sUnion_of_mem <| h ht'
#align set.sUnion_mono Set.unionₛ_mono
-/

/- warning: set.Union_subset_Union_const -> Set.unionᵢ_subset_unionᵢ_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι₂ : Sort.{u3}} {s : Set.{u1} α}, (ι -> ι₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s)) (Set.unionᵢ.{u1, u3} α ι₂ (fun (j : ι₂) => s)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι₂ : Sort.{u1}} {s : Set.{u3} α}, (ι -> ι₂) -> (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => s)) (Set.unionᵢ.{u3, u1} α ι₂ (fun (j : ι₂) => s)))
Case conversion may be inaccurate. Consider using '#align set.Union_subset_Union_const Set.unionᵢ_subset_unionᵢ_constₓ'. -/
theorem unionᵢ_subset_unionᵢ_const {s : Set α} (h : ι → ι₂) : (⋃ i : ι, s) ⊆ ⋃ j : ι₂, s :=
  @supᵢ_const_mono (Set α) ι ι₂ _ s h
#align set.Union_subset_Union_const Set.unionᵢ_subset_unionᵢ_const

/- warning: set.Union_singleton_eq_range -> Set.unionᵢ_singleton_eq_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) (f x))) (Set.range.{u2, succ u1} β α f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) (f x))) (Set.range.{u1, succ u2} β α f)
Case conversion may be inaccurate. Consider using '#align set.Union_singleton_eq_range Set.unionᵢ_singleton_eq_rangeₓ'. -/
@[simp]
theorem unionᵢ_singleton_eq_range {α β : Type _} (f : α → β) : (⋃ x : α, {f x}) = range f :=
  by
  ext x
  simp [@eq_comm _ x]
#align set.Union_singleton_eq_range Set.unionᵢ_singleton_eq_range

#print Set.unionᵢ_of_singleton /-
theorem unionᵢ_of_singleton (α : Type _) : (⋃ x, {x} : Set α) = univ := by simp
#align set.Union_of_singleton Set.unionᵢ_of_singleton
-/

#print Set.unionᵢ_of_singleton_coe /-
theorem unionᵢ_of_singleton_coe (s : Set α) : (⋃ i : s, {i} : Set α) = s := by simp
#align set.Union_of_singleton_coe Set.unionᵢ_of_singleton_coe
-/

#print Set.unionₛ_eq_bunionᵢ /-
theorem unionₛ_eq_bunionᵢ {s : Set (Set α)} : ⋃₀ s = ⋃ (i : Set α) (h : i ∈ s), i := by
  rw [← sUnion_image, image_id']
#align set.sUnion_eq_bUnion Set.unionₛ_eq_bunionᵢ
-/

#print Set.interₛ_eq_binterᵢ /-
theorem interₛ_eq_binterᵢ {s : Set (Set α)} : ⋂₀ s = ⋂ (i : Set α) (h : i ∈ s), i := by
  rw [← sInter_image, image_id']
#align set.sInter_eq_bInter Set.interₛ_eq_binterᵢ
-/

#print Set.unionₛ_eq_unionᵢ /-
theorem unionₛ_eq_unionᵢ {s : Set (Set α)} : ⋃₀ s = ⋃ i : s, i := by
  simp only [← sUnion_range, Subtype.range_coe]
#align set.sUnion_eq_Union Set.unionₛ_eq_unionᵢ
-/

#print Set.interₛ_eq_interᵢ /-
theorem interₛ_eq_interᵢ {s : Set (Set α)} : ⋂₀ s = ⋂ i : s, i := by
  simp only [← sInter_range, Subtype.range_coe]
#align set.sInter_eq_Inter Set.interₛ_eq_interᵢ
-/

#print Set.unionᵢ_of_empty /-
@[simp]
theorem unionᵢ_of_empty [IsEmpty ι] (s : ι → Set α) : (⋃ i, s i) = ∅ :=
  supᵢ_of_empty _
#align set.Union_of_empty Set.unionᵢ_of_empty
-/

#print Set.interᵢ_of_empty /-
@[simp]
theorem interᵢ_of_empty [IsEmpty ι] (s : ι → Set α) : (⋂ i, s i) = univ :=
  infᵢ_of_empty _
#align set.Inter_of_empty Set.interᵢ_of_empty
-/

/- warning: set.union_eq_Union -> Set.union_eq_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) (Set.unionᵢ.{u1, 1} α Bool (fun (b : Bool) => cond.{u1} (Set.{u1} α) b s₁ s₂))
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂) (Set.unionᵢ.{u1, 1} α Bool (fun (b : Bool) => cond.{u1} (Set.{u1} α) b s₁ s₂))
Case conversion may be inaccurate. Consider using '#align set.union_eq_Union Set.union_eq_unionᵢₓ'. -/
theorem union_eq_unionᵢ {s₁ s₂ : Set α} : s₁ ∪ s₂ = ⋃ b : Bool, cond b s₁ s₂ :=
  sup_eq_supᵢ s₁ s₂
#align set.union_eq_Union Set.union_eq_unionᵢ

/- warning: set.inter_eq_Inter -> Set.inter_eq_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) (Set.interᵢ.{u1, 1} α Bool (fun (b : Bool) => cond.{u1} (Set.{u1} α) b s₁ s₂))
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂) (Set.interᵢ.{u1, 1} α Bool (fun (b : Bool) => cond.{u1} (Set.{u1} α) b s₁ s₂))
Case conversion may be inaccurate. Consider using '#align set.inter_eq_Inter Set.inter_eq_interᵢₓ'. -/
theorem inter_eq_interᵢ {s₁ s₂ : Set α} : s₁ ∩ s₂ = ⋂ b : Bool, cond b s₁ s₂ :=
  inf_eq_infᵢ s₁ s₂
#align set.inter_eq_Inter Set.inter_eq_interᵢ

/- warning: set.sInter_union_sInter -> Set.interₛ_union_interₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {S : Set.{u1} (Set.{u1} α)} {T : Set.{u1} (Set.{u1} α)}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Set.interₛ.{u1} α S) (Set.interₛ.{u1} α T)) (Set.interᵢ.{u1, succ u1} α (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) (fun (p : Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) => Set.interᵢ.{u1, 0} α (Membership.Mem.{u1, u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) (Set.hasMem.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) p (Set.prod.{u1, u1} (Set.{u1} α) (Set.{u1} α) S T)) (fun (H : Membership.Mem.{u1, u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) (Set.hasMem.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) p (Set.prod.{u1, u1} (Set.{u1} α) (Set.{u1} α) S T)) => Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Prod.fst.{u1, u1} (Set.{u1} α) (Set.{u1} α) p) (Prod.snd.{u1, u1} (Set.{u1} α) (Set.{u1} α) p))))
but is expected to have type
  forall {α : Type.{u1}} {S : Set.{u1} (Set.{u1} α)} {T : Set.{u1} (Set.{u1} α)}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Set.interₛ.{u1} α S) (Set.interₛ.{u1} α T)) (Set.interᵢ.{u1, succ u1} α (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) (fun (p : Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) => Set.interᵢ.{u1, 0} α (Membership.mem.{u1, u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) (Set.instMembershipSet.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) p (Set.prod.{u1, u1} (Set.{u1} α) (Set.{u1} α) S T)) (fun (H : Membership.mem.{u1, u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) (Set.instMembershipSet.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) p (Set.prod.{u1, u1} (Set.{u1} α) (Set.{u1} α) S T)) => Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Prod.fst.{u1, u1} (Set.{u1} α) (Set.{u1} α) p) (Prod.snd.{u1, u1} (Set.{u1} α) (Set.{u1} α) p))))
Case conversion may be inaccurate. Consider using '#align set.sInter_union_sInter Set.interₛ_union_interₛₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem interₛ_union_interₛ {S T : Set (Set α)} :
    ⋂₀ S ∪ ⋂₀ T = ⋂ p ∈ S ×ˢ T, (p : Set α × Set α).1 ∪ p.2 :=
  infₛ_sup_infₛ
#align set.sInter_union_sInter Set.interₛ_union_interₛ

/- warning: set.sUnion_inter_sUnion -> Set.unionₛ_inter_unionₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} (Set.{u1} α)} {t : Set.{u1} (Set.{u1} α)}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.unionₛ.{u1} α s) (Set.unionₛ.{u1} α t)) (Set.unionᵢ.{u1, succ u1} α (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) (fun (p : Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) (Set.hasMem.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) p (Set.prod.{u1, u1} (Set.{u1} α) (Set.{u1} α) s t)) (fun (H : Membership.Mem.{u1, u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) (Set.hasMem.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) p (Set.prod.{u1, u1} (Set.{u1} α) (Set.{u1} α) s t)) => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Prod.fst.{u1, u1} (Set.{u1} α) (Set.{u1} α) p) (Prod.snd.{u1, u1} (Set.{u1} α) (Set.{u1} α) p))))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} (Set.{u1} α)} {t : Set.{u1} (Set.{u1} α)}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.unionₛ.{u1} α s) (Set.unionₛ.{u1} α t)) (Set.unionᵢ.{u1, succ u1} α (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) (fun (p : Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) (Set.instMembershipSet.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) p (Set.prod.{u1, u1} (Set.{u1} α) (Set.{u1} α) s t)) (fun (H : Membership.mem.{u1, u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α)) (Set.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) (Set.instMembershipSet.{u1} (Prod.{u1, u1} (Set.{u1} α) (Set.{u1} α))) p (Set.prod.{u1, u1} (Set.{u1} α) (Set.{u1} α) s t)) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Prod.fst.{u1, u1} (Set.{u1} α) (Set.{u1} α) p) (Prod.snd.{u1, u1} (Set.{u1} α) (Set.{u1} α) p))))
Case conversion may be inaccurate. Consider using '#align set.sUnion_inter_sUnion Set.unionₛ_inter_unionₛₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem unionₛ_inter_unionₛ {s t : Set (Set α)} :
    ⋃₀ s ∩ ⋃₀ t = ⋃ p ∈ s ×ˢ t, (p : Set α × Set α).1 ∩ p.2 :=
  supₛ_inf_supₛ
#align set.sUnion_inter_sUnion Set.unionₛ_inter_unionₛ

/- warning: set.bUnion_Union -> Set.bunionᵢ_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} (s : ι -> (Set.{u1} α)) (t : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i))) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i))) => t x))) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s i)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s i)) => t x))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u3} α)) (t : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u3} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i))) (fun (H : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i))) => t x))) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => Set.unionᵢ.{u2, succ u3} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (s i)) (fun (H : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (s i)) => t x))))
Case conversion may be inaccurate. Consider using '#align set.bUnion_Union Set.bunionᵢ_unionᵢₓ'. -/
theorem bunionᵢ_unionᵢ (s : ι → Set α) (t : α → Set β) :
    (⋃ x ∈ ⋃ i, s i, t x) = ⋃ (i) (x ∈ s i), t x := by simp [@Union_comm _ ι]
#align set.bUnion_Union Set.bunionᵢ_unionᵢ

/- warning: set.bInter_Union -> Set.binterᵢ_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} (s : ι -> (Set.{u1} α)) (t : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i))) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i))) => t x))) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s i)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s i)) => t x))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u3} α)) (t : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, succ u3} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i))) (fun (H : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i))) => t x))) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => Set.interᵢ.{u2, succ u3} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (s i)) (fun (H : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (s i)) => t x))))
Case conversion may be inaccurate. Consider using '#align set.bInter_Union Set.binterᵢ_unionᵢₓ'. -/
theorem binterᵢ_unionᵢ (s : ι → Set α) (t : α → Set β) :
    (⋂ x ∈ ⋃ i, s i, t x) = ⋂ (i) (x ∈ s i), t x := by simp [@Inter_comm _ ι]
#align set.bInter_Union Set.binterᵢ_unionᵢ

/- warning: set.sUnion_Union -> Set.unionₛ_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} (Set.{u1} α))), Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α (Set.unionᵢ.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => s i))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionₛ.{u1} α (s i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} (Set.{u2} α))), Eq.{succ u2} (Set.{u2} α) (Set.unionₛ.{u2} α (Set.unionᵢ.{u2, u1} (Set.{u2} α) ι (fun (i : ι) => s i))) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => Set.unionₛ.{u2} α (s i)))
Case conversion may be inaccurate. Consider using '#align set.sUnion_Union Set.unionₛ_unionᵢₓ'. -/
theorem unionₛ_unionᵢ (s : ι → Set (Set α)) : (⋃₀ ⋃ i, s i) = ⋃ i, ⋃₀ s i := by
  simp only [sUnion_eq_bUnion, bUnion_Union]
#align set.sUnion_Union Set.unionₛ_unionᵢ

/- warning: set.sInter_Union -> Set.interₛ_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} (Set.{u1} α))), Eq.{succ u1} (Set.{u1} α) (Set.interₛ.{u1} α (Set.unionᵢ.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => s i))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interₛ.{u1} α (s i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} (Set.{u2} α))), Eq.{succ u2} (Set.{u2} α) (Set.interₛ.{u2} α (Set.unionᵢ.{u2, u1} (Set.{u2} α) ι (fun (i : ι) => s i))) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Set.interₛ.{u2} α (s i)))
Case conversion may be inaccurate. Consider using '#align set.sInter_Union Set.interₛ_unionᵢₓ'. -/
theorem interₛ_unionᵢ (s : ι → Set (Set α)) : (⋂₀ ⋃ i, s i) = ⋂ i, ⋂₀ s i := by
  simp only [sInter_eq_bInter, bInter_Union]
#align set.sInter_Union Set.interₛ_unionᵢ

/- warning: set.Union_range_eq_sUnion -> Set.unionᵢ_range_eq_unionₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (C : Set.{u1} (Set.{u1} α)) {f : forall (s : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) C), β -> (coeSort.{succ u1, succ (succ u1)} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) C) Type.{u1} (coeSortTrans.{succ (succ u1), succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) C) (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (coeBaseAux.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) C) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) x C)))) s)}, (forall (s : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) C), Function.Surjective.{succ u2, succ u1} β (coeSort.{succ u1, succ (succ u1)} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) C) Type.{u1} (coeSortTrans.{succ (succ u1), succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) C) (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (coeBaseAux.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) C) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) x C)))) s) (f s)) -> (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α β (fun (y : β) => Set.range.{u1, succ u1} α (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) C) (fun (s : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) C) => Subtype.val.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCoeTAux.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) C) (Set.{u1} α) (coeBaseAux.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} α)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} α)) C) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) x C))) s)) (f s y)))) (Set.unionₛ.{u1} α C))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (C : Set.{u2} (Set.{u2} α)) {f : forall (s : Set.Elem.{u2} (Set.{u2} α) C), β -> (Set.Elem.{u2} α (Subtype.val.{succ u2} (Set.{u2} α) (fun (x : Set.{u2} α) => Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) x C) s))}, (forall (s : Set.Elem.{u2} (Set.{u2} α) C), Function.Surjective.{succ u1, succ u2} β (Set.Elem.{u2} α (Subtype.val.{succ u2} (Set.{u2} α) (fun (x : Set.{u2} α) => Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) x C) s)) (f s)) -> (Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, succ u1} α β (fun (y : β) => Set.range.{u2, succ u2} α (Set.Elem.{u2} (Set.{u2} α) C) (fun (s : Set.Elem.{u2} (Set.{u2} α) C) => Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Subtype.val.{succ u2} (Set.{u2} α) (fun (x : Set.{u2} α) => Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) x C) s)) (f s y)))) (Set.unionₛ.{u2} α C))
Case conversion may be inaccurate. Consider using '#align set.Union_range_eq_sUnion Set.unionᵢ_range_eq_unionₛₓ'. -/
theorem unionᵢ_range_eq_unionₛ {α β : Type _} (C : Set (Set α)) {f : ∀ s : C, β → s}
    (hf : ∀ s : C, Surjective (f s)) : (⋃ y : β, range fun s : C => (f s y).val) = ⋃₀ C :=
  by
  ext x; constructor
  · rintro ⟨s, ⟨y, rfl⟩, ⟨s, hs⟩, rfl⟩
    refine' ⟨_, hs, _⟩
    exact (f ⟨s, hs⟩ y).2
  · rintro ⟨s, hs, hx⟩
    cases' hf ⟨s, hs⟩ ⟨x, hx⟩ with y hy
    refine' ⟨_, ⟨y, rfl⟩, ⟨s, hs⟩, _⟩
    exact congr_arg Subtype.val hy
#align set.Union_range_eq_sUnion Set.unionᵢ_range_eq_unionₛ

/- warning: set.Union_range_eq_Union -> Set.unionᵢ_range_eq_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} (C : ι -> (Set.{u1} α)) {f : forall (x : ι), β -> (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (C x))}, (forall (x : ι), Function.Surjective.{succ u2, succ u1} β (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (C x)) (f x)) -> (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α β (fun (y : β) => Set.range.{u1, u3} α ι (fun (x : ι) => Subtype.val.{succ u1} α (fun (x_1 : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x_1 (C x)) (f x y)))) (Set.unionᵢ.{u1, u3} α ι (fun (x : ι) => C x)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} (C : ι -> (Set.{u3} α)) {f : forall (x : ι), β -> (Set.Elem.{u3} α (C x))}, (forall (x : ι), Function.Surjective.{succ u2, succ u3} β (Set.Elem.{u3} α (C x)) (f x)) -> (Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, succ u2} α β (fun (y : β) => Set.range.{u3, u1} α ι (fun (x : ι) => Subtype.val.{succ u3} α (fun (x_1 : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x_1 (C x)) (f x y)))) (Set.unionᵢ.{u3, u1} α ι (fun (x : ι) => C x)))
Case conversion may be inaccurate. Consider using '#align set.Union_range_eq_Union Set.unionᵢ_range_eq_unionᵢₓ'. -/
theorem unionᵢ_range_eq_unionᵢ (C : ι → Set α) {f : ∀ x : ι, β → C x}
    (hf : ∀ x : ι, Surjective (f x)) : (⋃ y : β, range fun x : ι => (f x y).val) = ⋃ x, C x :=
  by
  ext x; rw [mem_Union, mem_Union]; constructor
  · rintro ⟨y, i, rfl⟩
    exact ⟨i, (f i y).2⟩
  · rintro ⟨i, hx⟩
    cases' hf i ⟨x, hx⟩ with y hy
    exact ⟨y, i, congr_arg Subtype.val hy⟩
#align set.Union_range_eq_Union Set.unionᵢ_range_eq_unionᵢ

/- warning: set.union_distrib_Inter_left -> Set.union_distrib_interᵢ_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} α)) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t (s i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} α)) (t : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) t (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => s i))) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) t (s i)))
Case conversion may be inaccurate. Consider using '#align set.union_distrib_Inter_left Set.union_distrib_interᵢ_leftₓ'. -/
theorem union_distrib_interᵢ_left (s : ι → Set α) (t : Set α) : (t ∪ ⋂ i, s i) = ⋂ i, t ∪ s i :=
  sup_infᵢ_eq _ _
#align set.union_distrib_Inter_left Set.union_distrib_interᵢ_left

/- warning: set.union_distrib_Inter₂_left -> Set.union_distrib_interᵢ₂_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} (s : Set.{u1} α) (t : forall (i : ι), (κ i) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (t i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} (s : Set.{u3} α) (t : forall (i : ι), (κ i) -> (Set.{u3} α)), Eq.{succ u3} (Set.{u3} α) (Union.union.{u3} (Set.{u3} α) (Set.instUnionSet.{u3} α) s (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => Union.union.{u3} (Set.{u3} α) (Set.instUnionSet.{u3} α) s (t i j))))
Case conversion may be inaccurate. Consider using '#align set.union_distrib_Inter₂_left Set.union_distrib_interᵢ₂_leftₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem union_distrib_interᵢ₂_left (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j := by simp_rw [union_distrib_Inter_left]
#align set.union_distrib_Inter₂_left Set.union_distrib_interᵢ₂_left

/- warning: set.union_distrib_Inter_right -> Set.union_distrib_interᵢ_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (s : ι -> (Set.{u1} α)) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i)) t) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (s i) t))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u2} α)) (t : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => s i)) t) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (s i) t))
Case conversion may be inaccurate. Consider using '#align set.union_distrib_Inter_right Set.union_distrib_interᵢ_rightₓ'. -/
theorem union_distrib_interᵢ_right (s : ι → Set α) (t : Set α) : (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
  infᵢ_sup_eq _ _
#align set.union_distrib_Inter_right Set.union_distrib_interᵢ_right

/- warning: set.union_distrib_Inter₂_right -> Set.union_distrib_interᵢ₂_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} (s : forall (i : ι), (κ i) -> (Set.{u1} α)) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) t) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (s i j) t)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} (s : forall (i : ι), (κ i) -> (Set.{u3} α)) (t : Set.{u3} α), Eq.{succ u3} (Set.{u3} α) (Union.union.{u3} (Set.{u3} α) (Set.instUnionSet.{u3} α) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) t) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => Union.union.{u3} (Set.{u3} α) (Set.instUnionSet.{u3} α) (s i j) t)))
Case conversion may be inaccurate. Consider using '#align set.union_distrib_Inter₂_right Set.union_distrib_interᵢ₂_rightₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem union_distrib_interᵢ₂_right (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t := by simp_rw [union_distrib_Inter_right]
#align set.union_distrib_Inter₂_right Set.union_distrib_interᵢ₂_right

section Function

/-! ### `maps_to` -/


/- warning: set.maps_to_sUnion -> Set.mapsTo_unionₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {S : Set.{u1} (Set.{u1} α)} {t : Set.{u2} β} {f : α -> β}, (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s S) -> (Set.MapsTo.{u1, u2} α β f s t)) -> (Set.MapsTo.{u1, u2} α β f (Set.unionₛ.{u1} α S) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {S : Set.{u2} (Set.{u2} α)} {t : Set.{u1} β} {f : α -> β}, (forall (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) s S) -> (Set.MapsTo.{u2, u1} α β f s t)) -> (Set.MapsTo.{u2, u1} α β f (Set.unionₛ.{u2} α S) t)
Case conversion may be inaccurate. Consider using '#align set.maps_to_sUnion Set.mapsTo_unionₛₓ'. -/
theorem mapsTo_unionₛ {S : Set (Set α)} {t : Set β} {f : α → β} (H : ∀ s ∈ S, MapsTo f s t) :
    MapsTo f (⋃₀ S) t := fun x ⟨s, hs, hx⟩ => H s hs hx
#align set.maps_to_sUnion Set.mapsTo_unionₛ

/- warning: set.maps_to_Union -> Set.mapsTo_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {s : ι -> (Set.{u1} α)} {t : Set.{u2} β} {f : α -> β}, (forall (i : ι), Set.MapsTo.{u1, u2} α β f (s i) t) -> (Set.MapsTo.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i)) t)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u3} α)} {t : Set.{u2} β} {f : α -> β}, (forall (i : ι), Set.MapsTo.{u3, u2} α β f (s i) t) -> (Set.MapsTo.{u3, u2} α β f (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i)) t)
Case conversion may be inaccurate. Consider using '#align set.maps_to_Union Set.mapsTo_unionᵢₓ'. -/
theorem mapsTo_unionᵢ {s : ι → Set α} {t : Set β} {f : α → β} (H : ∀ i, MapsTo f (s i) t) :
    MapsTo f (⋃ i, s i) t :=
  maps_to_sUnion <| forall_range_iff.2 H
#align set.maps_to_Union Set.mapsTo_unionᵢ

/- warning: set.maps_to_Union₂ -> Set.mapsTo_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {t : Set.{u2} β} {f : α -> β}, (forall (i : ι) (j : κ i), Set.MapsTo.{u1, u2} α β f (s i j) t) -> (Set.MapsTo.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => Set.unionᵢ.{u1, u4} α (κ i) (fun (j : κ i) => s i j))) t)
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u4} α)} {t : Set.{u3} β} {f : α -> β}, (forall (i : ι) (j : κ i), Set.MapsTo.{u4, u3} α β f (s i j) t) -> (Set.MapsTo.{u4, u3} α β f (Set.unionᵢ.{u4, u2} α ι (fun (i : ι) => Set.unionᵢ.{u4, u1} α (κ i) (fun (j : κ i) => s i j))) t)
Case conversion may be inaccurate. Consider using '#align set.maps_to_Union₂ Set.mapsTo_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mapsTo_unionᵢ₂ {s : ∀ i, κ i → Set α} {t : Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) t) : MapsTo f (⋃ (i) (j), s i j) t :=
  maps_to_Union fun i => mapsTo_unionᵢ (H i)
#align set.maps_to_Union₂ Set.mapsTo_unionᵢ₂

/- warning: set.maps_to_Union_Union -> Set.mapsTo_unionᵢ_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.MapsTo.{u1, u2} α β f (s i) (t i)) -> (Set.MapsTo.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => t i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u3} α)} {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.MapsTo.{u3, u2} α β f (s i) (t i)) -> (Set.MapsTo.{u3, u2} α β f (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.maps_to_Union_Union Set.mapsTo_unionᵢ_unionᵢₓ'. -/
theorem mapsTo_unionᵢ_unionᵢ {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, MapsTo f (s i) (t i)) : MapsTo f (⋃ i, s i) (⋃ i, t i) :=
  maps_to_Union fun i => (H i).mono (Subset.refl _) (subset_unionᵢ t i)
#align set.maps_to_Union_Union Set.mapsTo_unionᵢ_unionᵢ

/- warning: set.maps_to_Union₂_Union₂ -> Set.mapsTo_unionᵢ₂_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {t : forall (i : ι), (κ i) -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι) (j : κ i), Set.MapsTo.{u1, u2} α β f (s i j) (t i j)) -> (Set.MapsTo.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => Set.unionᵢ.{u1, u4} α (κ i) (fun (j : κ i) => s i j))) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, u4} β (κ i) (fun (j : κ i) => t i j))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u4} α)} {t : forall (i : ι), (κ i) -> (Set.{u3} β)} {f : α -> β}, (forall (i : ι) (j : κ i), Set.MapsTo.{u4, u3} α β f (s i j) (t i j)) -> (Set.MapsTo.{u4, u3} α β f (Set.unionᵢ.{u4, u2} α ι (fun (i : ι) => Set.unionᵢ.{u4, u1} α (κ i) (fun (j : κ i) => s i j))) (Set.unionᵢ.{u3, u2} β ι (fun (i : ι) => Set.unionᵢ.{u3, u1} β (κ i) (fun (j : κ i) => t i j))))
Case conversion may be inaccurate. Consider using '#align set.maps_to_Union₂_Union₂ Set.mapsTo_unionᵢ₂_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mapsTo_unionᵢ₂_unionᵢ₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  maps_to_Union_Union fun i => mapsTo_unionᵢ_unionᵢ (H i)
#align set.maps_to_Union₂_Union₂ Set.mapsTo_unionᵢ₂_unionᵢ₂

/- warning: set.maps_to_sInter -> Set.mapsTo_interₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {T : Set.{u2} (Set.{u2} β)} {f : α -> β}, (forall (t : Set.{u2} β), (Membership.Mem.{u2, u2} (Set.{u2} β) (Set.{u2} (Set.{u2} β)) (Set.hasMem.{u2} (Set.{u2} β)) t T) -> (Set.MapsTo.{u1, u2} α β f s t)) -> (Set.MapsTo.{u1, u2} α β f s (Set.interₛ.{u2} β T))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {T : Set.{u1} (Set.{u1} β)} {f : α -> β}, (forall (t : Set.{u1} β), (Membership.mem.{u1, u1} (Set.{u1} β) (Set.{u1} (Set.{u1} β)) (Set.instMembershipSet.{u1} (Set.{u1} β)) t T) -> (Set.MapsTo.{u2, u1} α β f s t)) -> (Set.MapsTo.{u2, u1} α β f s (Set.interₛ.{u1} β T))
Case conversion may be inaccurate. Consider using '#align set.maps_to_sInter Set.mapsTo_interₛₓ'. -/
theorem mapsTo_interₛ {s : Set α} {T : Set (Set β)} {f : α → β} (H : ∀ t ∈ T, MapsTo f s t) :
    MapsTo f s (⋂₀ T) := fun x hx t ht => H t ht hx
#align set.maps_to_sInter Set.mapsTo_interₛ

/- warning: set.maps_to_Inter -> Set.mapsTo_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {s : Set.{u1} α} {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.MapsTo.{u1, u2} α β f s (t i)) -> (Set.MapsTo.{u1, u2} α β f s (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => t i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} {s : Set.{u3} α} {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.MapsTo.{u3, u2} α β f s (t i)) -> (Set.MapsTo.{u3, u2} α β f s (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.maps_to_Inter Set.mapsTo_interᵢₓ'. -/
theorem mapsTo_interᵢ {s : Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, MapsTo f s (t i)) :
    MapsTo f s (⋂ i, t i) := fun x hx => mem_interᵢ.2 fun i => H i hx
#align set.maps_to_Inter Set.mapsTo_interᵢ

/- warning: set.maps_to_Inter₂ -> Set.mapsTo_interᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} {s : Set.{u1} α} {t : forall (i : ι), (κ i) -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι) (j : κ i), Set.MapsTo.{u1, u2} α β f s (t i j)) -> (Set.MapsTo.{u1, u2} α β f s (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.interᵢ.{u2, u4} β (κ i) (fun (j : κ i) => t i j))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : Set.{u4} α} {t : forall (i : ι), (κ i) -> (Set.{u3} β)} {f : α -> β}, (forall (i : ι) (j : κ i), Set.MapsTo.{u4, u3} α β f s (t i j)) -> (Set.MapsTo.{u4, u3} α β f s (Set.interᵢ.{u3, u2} β ι (fun (i : ι) => Set.interᵢ.{u3, u1} β (κ i) (fun (j : κ i) => t i j))))
Case conversion may be inaccurate. Consider using '#align set.maps_to_Inter₂ Set.mapsTo_interᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mapsTo_interᵢ₂ {s : Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f s (t i j)) : MapsTo f s (⋂ (i) (j), t i j) :=
  maps_to_Inter fun i => mapsTo_interᵢ (H i)
#align set.maps_to_Inter₂ Set.mapsTo_interᵢ₂

/- warning: set.maps_to_Inter_Inter -> Set.mapsTo_interᵢ_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.MapsTo.{u1, u2} α β f (s i) (t i)) -> (Set.MapsTo.{u1, u2} α β f (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => t i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u3} α)} {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.MapsTo.{u3, u2} α β f (s i) (t i)) -> (Set.MapsTo.{u3, u2} α β f (Set.interᵢ.{u3, u1} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.maps_to_Inter_Inter Set.mapsTo_interᵢ_interᵢₓ'. -/
theorem mapsTo_interᵢ_interᵢ {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, MapsTo f (s i) (t i)) : MapsTo f (⋂ i, s i) (⋂ i, t i) :=
  maps_to_Inter fun i => (H i).mono (interᵢ_subset s i) (Subset.refl _)
#align set.maps_to_Inter_Inter Set.mapsTo_interᵢ_interᵢ

/- warning: set.maps_to_Inter₂_Inter₂ -> Set.mapsTo_interᵢ₂_interᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {t : forall (i : ι), (κ i) -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι) (j : κ i), Set.MapsTo.{u1, u2} α β f (s i j) (t i j)) -> (Set.MapsTo.{u1, u2} α β f (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => Set.interᵢ.{u1, u4} α (κ i) (fun (j : κ i) => s i j))) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.interᵢ.{u2, u4} β (κ i) (fun (j : κ i) => t i j))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u4} α)} {t : forall (i : ι), (κ i) -> (Set.{u3} β)} {f : α -> β}, (forall (i : ι) (j : κ i), Set.MapsTo.{u4, u3} α β f (s i j) (t i j)) -> (Set.MapsTo.{u4, u3} α β f (Set.interᵢ.{u4, u2} α ι (fun (i : ι) => Set.interᵢ.{u4, u1} α (κ i) (fun (j : κ i) => s i j))) (Set.interᵢ.{u3, u2} β ι (fun (i : ι) => Set.interᵢ.{u3, u1} β (κ i) (fun (j : κ i) => t i j))))
Case conversion may be inaccurate. Consider using '#align set.maps_to_Inter₂_Inter₂ Set.mapsTo_interᵢ₂_interᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mapsTo_interᵢ₂_interᵢ₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋂ (i) (j), s i j) (⋂ (i) (j), t i j) :=
  maps_to_Inter_Inter fun i => mapsTo_interᵢ_interᵢ (H i)
#align set.maps_to_Inter₂_Inter₂ Set.mapsTo_interᵢ₂_interᵢ₂

/- warning: set.image_Inter_subset -> Set.image_interᵢ_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} (s : ι -> (Set.{u1} α)) (f : α -> β), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => s i))) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.image.{u1, u2} α β f (s i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} (s : ι -> (Set.{u3} α)) (f : α -> β), HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (Set.image.{u3, u2} α β f (Set.interᵢ.{u3, u1} α ι (fun (i : ι) => s i))) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => Set.image.{u3, u2} α β f (s i)))
Case conversion may be inaccurate. Consider using '#align set.image_Inter_subset Set.image_interᵢ_subsetₓ'. -/
theorem image_interᵢ_subset (s : ι → Set α) (f : α → β) : (f '' ⋂ i, s i) ⊆ ⋂ i, f '' s i :=
  (maps_to_Inter_Inter fun i => mapsTo_image f (s i)).image_subset
#align set.image_Inter_subset Set.image_interᵢ_subset

/- warning: set.image_Inter₂_subset -> Set.image_interᵢ₂_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} (s : forall (i : ι), (κ i) -> (Set.{u1} α)) (f : α -> β), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => Set.interᵢ.{u1, u4} α (κ i) (fun (j : κ i) => s i j)))) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.interᵢ.{u2, u4} β (κ i) (fun (j : κ i) => Set.image.{u1, u2} α β f (s i j))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} (s : forall (i : ι), (κ i) -> (Set.{u4} α)) (f : α -> β), HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (Set.image.{u4, u3} α β f (Set.interᵢ.{u4, u2} α ι (fun (i : ι) => Set.interᵢ.{u4, u1} α (κ i) (fun (j : κ i) => s i j)))) (Set.interᵢ.{u3, u2} β ι (fun (i : ι) => Set.interᵢ.{u3, u1} β (κ i) (fun (j : κ i) => Set.image.{u4, u3} α β f (s i j))))
Case conversion may be inaccurate. Consider using '#align set.image_Inter₂_subset Set.image_interᵢ₂_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image_interᵢ₂_subset (s : ∀ i, κ i → Set α) (f : α → β) :
    (f '' ⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), f '' s i j :=
  (maps_to_Inter₂_Inter₂ fun i hi => mapsTo_image f (s i hi)).image_subset
#align set.image_Inter₂_subset Set.image_interᵢ₂_subset

/- warning: set.image_sInter_subset -> Set.image_interₛ_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (S : Set.{u1} (Set.{u1} α)) (f : α -> β), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f (Set.interₛ.{u1} α S)) (Set.interᵢ.{u2, succ u1} β (Set.{u1} α) (fun (s : Set.{u1} α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s S) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s S) => Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (S : Set.{u2} (Set.{u2} α)) (f : α -> β), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.image.{u2, u1} α β f (Set.interₛ.{u2} α S)) (Set.interᵢ.{u1, succ u2} β (Set.{u2} α) (fun (s : Set.{u2} α) => Set.interᵢ.{u1, 0} β (Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) s S) (fun (H : Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) s S) => Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align set.image_sInter_subset Set.image_interₛ_subsetₓ'. -/
theorem image_interₛ_subset (S : Set (Set α)) (f : α → β) : f '' ⋂₀ S ⊆ ⋂ s ∈ S, f '' s :=
  by
  rw [sInter_eq_bInter]
  apply image_Inter₂_subset
#align set.image_sInter_subset Set.image_interₛ_subset

/-! ### `restrict_preimage` -/


section

open Function

variable (s : Set β) {f : α → β} {U : ι → Set β} (hU : unionᵢ U = univ)

include hU

/- warning: set.injective_iff_injective_of_Union_eq_univ -> Set.injective_iff_injective_of_unionᵢ_eq_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β} {U : ι -> (Set.{u2} β)}, (Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, u3} β ι U) (Set.univ.{u2} β)) -> (Iff (Function.Injective.{succ u1, succ u2} α β f) (forall (i : ι), Function.Injective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.preimage.{u1, u2} α β f (U i))) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (U i)) (Set.restrictPreimage.{u1, u2} α β (U i) f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Sort.{u3}} {f : α -> β} {U : ι -> (Set.{u1} β)}, (Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, u3} β ι U) (Set.univ.{u1} β)) -> (Iff (Function.Injective.{succ u2, succ u1} α β f) (forall (i : ι), Function.Injective.{succ u2, succ u1} (Set.Elem.{u2} α (Set.preimage.{u2, u1} α β f (U i))) (Set.Elem.{u1} β (U i)) (Set.restrictPreimage.{u2, u1} α β (U i) f)))
Case conversion may be inaccurate. Consider using '#align set.injective_iff_injective_of_Union_eq_univ Set.injective_iff_injective_of_unionᵢ_eq_univₓ'. -/
theorem injective_iff_injective_of_unionᵢ_eq_univ :
    Injective f ↔ ∀ i, Injective ((U i).restrictPreimage f) :=
  by
  refine' ⟨fun H i => (U i).restrict_preimage_injective H, fun H x y e => _⟩
  obtain ⟨i, hi⟩ :=
    set.mem_Union.mp
      (show f x ∈ Set.unionᵢ U by
        rw [hU]
        triv)
  injection @H i ⟨x, hi⟩ ⟨y, show f y ∈ U i from e ▸ hi⟩ (Subtype.ext e)
#align set.injective_iff_injective_of_Union_eq_univ Set.injective_iff_injective_of_unionᵢ_eq_univ

/- warning: set.surjective_iff_surjective_of_Union_eq_univ -> Set.surjective_iff_surjective_of_unionᵢ_eq_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β} {U : ι -> (Set.{u2} β)}, (Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, u3} β ι U) (Set.univ.{u2} β)) -> (Iff (Function.Surjective.{succ u1, succ u2} α β f) (forall (i : ι), Function.Surjective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.preimage.{u1, u2} α β f (U i))) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (U i)) (Set.restrictPreimage.{u1, u2} α β (U i) f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Sort.{u3}} {f : α -> β} {U : ι -> (Set.{u1} β)}, (Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, u3} β ι U) (Set.univ.{u1} β)) -> (Iff (Function.Surjective.{succ u2, succ u1} α β f) (forall (i : ι), Function.Surjective.{succ u2, succ u1} (Set.Elem.{u2} α (Set.preimage.{u2, u1} α β f (U i))) (Set.Elem.{u1} β (U i)) (Set.restrictPreimage.{u2, u1} α β (U i) f)))
Case conversion may be inaccurate. Consider using '#align set.surjective_iff_surjective_of_Union_eq_univ Set.surjective_iff_surjective_of_unionᵢ_eq_univₓ'. -/
theorem surjective_iff_surjective_of_unionᵢ_eq_univ :
    Surjective f ↔ ∀ i, Surjective ((U i).restrictPreimage f) :=
  by
  refine' ⟨fun H i => (U i).restrict_preimage_surjective H, fun H x => _⟩
  obtain ⟨i, hi⟩ :=
    set.mem_Union.mp
      (show x ∈ Set.unionᵢ U by
        rw [hU]
        triv)
  exact ⟨_, congr_arg Subtype.val (H i ⟨x, hi⟩).some_spec⟩
#align set.surjective_iff_surjective_of_Union_eq_univ Set.surjective_iff_surjective_of_unionᵢ_eq_univ

/- warning: set.bijective_iff_bijective_of_Union_eq_univ -> Set.bijective_iff_bijective_of_unionᵢ_eq_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β} {U : ι -> (Set.{u2} β)}, (Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, u3} β ι U) (Set.univ.{u2} β)) -> (Iff (Function.Bijective.{succ u1, succ u2} α β f) (forall (i : ι), Function.Bijective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.preimage.{u1, u2} α β f (U i))) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (U i)) (Set.restrictPreimage.{u1, u2} α β (U i) f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Sort.{u3}} {f : α -> β} {U : ι -> (Set.{u1} β)}, (Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, u3} β ι U) (Set.univ.{u1} β)) -> (Iff (Function.Bijective.{succ u2, succ u1} α β f) (forall (i : ι), Function.Bijective.{succ u2, succ u1} (Set.Elem.{u2} α (Set.preimage.{u2, u1} α β f (U i))) (Set.Elem.{u1} β (U i)) (Set.restrictPreimage.{u2, u1} α β (U i) f)))
Case conversion may be inaccurate. Consider using '#align set.bijective_iff_bijective_of_Union_eq_univ Set.bijective_iff_bijective_of_unionᵢ_eq_univₓ'. -/
theorem bijective_iff_bijective_of_unionᵢ_eq_univ :
    Bijective f ↔ ∀ i, Bijective ((U i).restrictPreimage f) := by
  simp_rw [bijective, forall_and, injective_iff_injective_of_Union_eq_univ hU,
    surjective_iff_surjective_of_Union_eq_univ hU]
#align set.bijective_iff_bijective_of_Union_eq_univ Set.bijective_iff_bijective_of_unionᵢ_eq_univ

end

/-! ### `inj_on` -/


/- warning: set.inj_on.image_Inter_eq -> Set.InjOn.image_interᵢ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : Nonempty.{u3} ι] {s : ι -> (Set.{u1} α)} {f : α -> β}, (Set.InjOn.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i))) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => s i))) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.image.{u1, u2} α β f (s i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Sort.{u3}} [_inst_1 : Nonempty.{u3} ι] {s : ι -> (Set.{u2} α)} {f : α -> β}, (Set.InjOn.{u2, u1} α β f (Set.unionᵢ.{u2, u3} α ι (fun (i : ι) => s i))) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (Set.interᵢ.{u2, u3} α ι (fun (i : ι) => s i))) (Set.interᵢ.{u1, u3} β ι (fun (i : ι) => Set.image.{u2, u1} α β f (s i))))
Case conversion may be inaccurate. Consider using '#align set.inj_on.image_Inter_eq Set.InjOn.image_interᵢ_eqₓ'. -/
theorem InjOn.image_interᵢ_eq [Nonempty ι] {s : ι → Set α} {f : α → β} (h : InjOn f (⋃ i, s i)) :
    (f '' ⋂ i, s i) = ⋂ i, f '' s i := by
  inhabit ι
  refine' subset.antisymm (image_Inter_subset s f) fun y hy => _
  simp only [mem_Inter, mem_image_iff_bex] at hy
  choose x hx hy using hy
  refine' ⟨x default, mem_Inter.2 fun i => _, hy _⟩
  suffices x default = x i by
    rw [this]
    apply hx
  replace hx : ∀ i, x i ∈ ⋃ j, s j := fun i => (subset_Union _ _) (hx i)
  apply h (hx _) (hx _)
  simp only [hy]
#align set.inj_on.image_Inter_eq Set.InjOn.image_interᵢ_eq

/- warning: set.inj_on.image_bInter_eq -> Set.InjOn.image_binterᵢ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {p : ι -> Prop} {s : forall (i : ι), (p i) -> (Set.{u1} α)}, (Exists.{u3} ι (fun (i : ι) => p i)) -> (forall {f : α -> β}, (Set.InjOn.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (p i) (fun (hi : p i) => s i hi)))) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => Set.interᵢ.{u1, 0} α (p i) (fun (hi : p i) => s i hi)))) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.interᵢ.{u2, 0} β (p i) (fun (hi : p i) => Set.image.{u1, u2} α β f (s i hi))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {ι : Sort.{u2}} {p : ι -> Prop} {s : forall (i : ι), (p i) -> (Set.{u3} α)}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (forall {f : α -> β}, (Set.InjOn.{u3, u1} α β f (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, 0} α (p i) (fun (hi : p i) => s i hi)))) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u3, u1} α β f (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, 0} α (p i) (fun (hi : p i) => s i hi)))) (Set.interᵢ.{u1, u2} β ι (fun (i : ι) => Set.interᵢ.{u1, 0} β (p i) (fun (hi : p i) => Set.image.{u3, u1} α β f (s i hi))))))
Case conversion may be inaccurate. Consider using '#align set.inj_on.image_bInter_eq Set.InjOn.image_binterᵢ_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
theorem InjOn.image_binterᵢ_eq {p : ι → Prop} {s : ∀ (i) (hi : p i), Set α} (hp : ∃ i, p i)
    {f : α → β} (h : InjOn f (⋃ (i) (hi), s i hi)) :
    (f '' ⋂ (i) (hi), s i hi) = ⋂ (i) (hi), f '' s i hi :=
  by
  simp only [Inter, infᵢ_subtype']
  haveI : Nonempty { i // p i } := nonempty_subtype.2 hp
  apply inj_on.image_Inter_eq
  simpa only [Union, supᵢ_subtype'] using h
#align set.inj_on.image_bInter_eq Set.InjOn.image_binterᵢ_eq

/- warning: set.image_Inter -> Set.image_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β}, (Function.Bijective.{succ u1, succ u2} α β f) -> (forall (s : ι -> (Set.{u1} α)), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => s i))) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.image.{u1, u2} α β f (s i))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} {f : α -> β}, (Function.Bijective.{succ u3, succ u2} α β f) -> (forall (s : ι -> (Set.{u3} α)), Eq.{succ u2} (Set.{u2} β) (Set.image.{u3, u2} α β f (Set.interᵢ.{u3, u1} α ι (fun (i : ι) => s i))) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => Set.image.{u3, u2} α β f (s i))))
Case conversion may be inaccurate. Consider using '#align set.image_Inter Set.image_interᵢₓ'. -/
theorem image_interᵢ {f : α → β} (hf : Bijective f) (s : ι → Set α) :
    (f '' ⋂ i, s i) = ⋂ i, f '' s i :=
  by
  cases isEmpty_or_nonempty ι
  · simp_rw [Inter_of_empty, image_univ_of_surjective hf.surjective]
  · exact (hf.injective.inj_on _).image_Inter_eq
#align set.image_Inter Set.image_interᵢ

/- warning: set.image_Inter₂ -> Set.image_interᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} {f : α -> β}, (Function.Bijective.{succ u1, succ u2} α β f) -> (forall (s : forall (i : ι), (κ i) -> (Set.{u1} α)), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => Set.interᵢ.{u1, u4} α (κ i) (fun (j : κ i) => s i j)))) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.interᵢ.{u2, u4} β (κ i) (fun (j : κ i) => Set.image.{u1, u2} α β f (s i j)))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {f : α -> β}, (Function.Bijective.{succ u4, succ u3} α β f) -> (forall (s : forall (i : ι), (κ i) -> (Set.{u4} α)), Eq.{succ u3} (Set.{u3} β) (Set.image.{u4, u3} α β f (Set.interᵢ.{u4, u2} α ι (fun (i : ι) => Set.interᵢ.{u4, u1} α (κ i) (fun (j : κ i) => s i j)))) (Set.interᵢ.{u3, u2} β ι (fun (i : ι) => Set.interᵢ.{u3, u1} β (κ i) (fun (j : κ i) => Set.image.{u4, u3} α β f (s i j)))))
Case conversion may be inaccurate. Consider using '#align set.image_Inter₂ Set.image_interᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image_interᵢ₂ {f : α → β} (hf : Bijective f) (s : ∀ i, κ i → Set α) :
    (f '' ⋂ (i) (j), s i j) = ⋂ (i) (j), f '' s i j := by simp_rw [image_Inter hf]
#align set.image_Inter₂ Set.image_interᵢ₂

/- warning: set.inj_on_Union_of_directed -> Set.inj_on_unionᵢ_of_directed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {s : ι -> (Set.{u1} α)}, (Directed.{u1, u3} (Set.{u1} α) ι (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α)) s) -> (forall {f : α -> β}, (forall (i : ι), Set.InjOn.{u1, u2} α β f (s i)) -> (Set.InjOn.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u3} α)}, (Directed.{u3, u2} (Set.{u3} α) ι (fun (x._@.Mathlib.Data.Set.Lattice._hyg.24834 : Set.{u3} α) (x._@.Mathlib.Data.Set.Lattice._hyg.24836 : Set.{u3} α) => HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) x._@.Mathlib.Data.Set.Lattice._hyg.24834 x._@.Mathlib.Data.Set.Lattice._hyg.24836) s) -> (forall {f : α -> β}, (forall (i : ι), Set.InjOn.{u3, u1} α β f (s i)) -> (Set.InjOn.{u3, u1} α β f (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => s i))))
Case conversion may be inaccurate. Consider using '#align set.inj_on_Union_of_directed Set.inj_on_unionᵢ_of_directedₓ'. -/
theorem inj_on_unionᵢ_of_directed {s : ι → Set α} (hs : Directed (· ⊆ ·) s) {f : α → β}
    (hf : ∀ i, InjOn f (s i)) : InjOn f (⋃ i, s i) :=
  by
  intro x hx y hy hxy
  rcases mem_Union.1 hx with ⟨i, hx⟩
  rcases mem_Union.1 hy with ⟨j, hy⟩
  rcases hs i j with ⟨k, hi, hj⟩
  exact hf k (hi hx) (hj hy) hxy
#align set.inj_on_Union_of_directed Set.inj_on_unionᵢ_of_directed

/-! ### `surj_on` -/


/- warning: set.surj_on_sUnion -> Set.surjOn_unionₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {T : Set.{u2} (Set.{u2} β)} {f : α -> β}, (forall (t : Set.{u2} β), (Membership.Mem.{u2, u2} (Set.{u2} β) (Set.{u2} (Set.{u2} β)) (Set.hasMem.{u2} (Set.{u2} β)) t T) -> (Set.SurjOn.{u1, u2} α β f s t)) -> (Set.SurjOn.{u1, u2} α β f s (Set.unionₛ.{u2} β T))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {T : Set.{u1} (Set.{u1} β)} {f : α -> β}, (forall (t : Set.{u1} β), (Membership.mem.{u1, u1} (Set.{u1} β) (Set.{u1} (Set.{u1} β)) (Set.instMembershipSet.{u1} (Set.{u1} β)) t T) -> (Set.SurjOn.{u2, u1} α β f s t)) -> (Set.SurjOn.{u2, u1} α β f s (Set.unionₛ.{u1} β T))
Case conversion may be inaccurate. Consider using '#align set.surj_on_sUnion Set.surjOn_unionₛₓ'. -/
theorem surjOn_unionₛ {s : Set α} {T : Set (Set β)} {f : α → β} (H : ∀ t ∈ T, SurjOn f s t) :
    SurjOn f s (⋃₀ T) := fun x ⟨t, ht, hx⟩ => H t ht hx
#align set.surj_on_sUnion Set.surjOn_unionₛ

/- warning: set.surj_on_Union -> Set.surjOn_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {s : Set.{u1} α} {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.SurjOn.{u1, u2} α β f s (t i)) -> (Set.SurjOn.{u1, u2} α β f s (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => t i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} {s : Set.{u3} α} {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.SurjOn.{u3, u2} α β f s (t i)) -> (Set.SurjOn.{u3, u2} α β f s (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.surj_on_Union Set.surjOn_unionᵢₓ'. -/
theorem surjOn_unionᵢ {s : Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, SurjOn f s (t i)) :
    SurjOn f s (⋃ i, t i) :=
  surj_on_sUnion <| forall_range_iff.2 H
#align set.surj_on_Union Set.surjOn_unionᵢ

/- warning: set.surj_on_Union_Union -> Set.surjOn_unionᵢ_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.SurjOn.{u1, u2} α β f (s i) (t i)) -> (Set.SurjOn.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => t i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u3} α)} {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.SurjOn.{u3, u2} α β f (s i) (t i)) -> (Set.SurjOn.{u3, u2} α β f (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.surj_on_Union_Union Set.surjOn_unionᵢ_unionᵢₓ'. -/
theorem surjOn_unionᵢ_unionᵢ {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) (t i)) : SurjOn f (⋃ i, s i) (⋃ i, t i) :=
  surj_on_Union fun i => (H i).mono (subset_unionᵢ _ _) (Subset.refl _)
#align set.surj_on_Union_Union Set.surjOn_unionᵢ_unionᵢ

/- warning: set.surj_on_Union₂ -> Set.surjOn_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} {s : Set.{u1} α} {t : forall (i : ι), (κ i) -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι) (j : κ i), Set.SurjOn.{u1, u2} α β f s (t i j)) -> (Set.SurjOn.{u1, u2} α β f s (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, u4} β (κ i) (fun (j : κ i) => t i j))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : Set.{u4} α} {t : forall (i : ι), (κ i) -> (Set.{u3} β)} {f : α -> β}, (forall (i : ι) (j : κ i), Set.SurjOn.{u4, u3} α β f s (t i j)) -> (Set.SurjOn.{u4, u3} α β f s (Set.unionᵢ.{u3, u2} β ι (fun (i : ι) => Set.unionᵢ.{u3, u1} β (κ i) (fun (j : κ i) => t i j))))
Case conversion may be inaccurate. Consider using '#align set.surj_on_Union₂ Set.surjOn_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem surjOn_unionᵢ₂ {s : Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, SurjOn f s (t i j)) : SurjOn f s (⋃ (i) (j), t i j) :=
  surj_on_Union fun i => surjOn_unionᵢ (H i)
#align set.surj_on_Union₂ Set.surjOn_unionᵢ₂

/- warning: set.surj_on_Union₂_Union₂ -> Set.surjOn_unionᵢ₂_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {t : forall (i : ι), (κ i) -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι) (j : κ i), Set.SurjOn.{u1, u2} α β f (s i j) (t i j)) -> (Set.SurjOn.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => Set.unionᵢ.{u1, u4} α (κ i) (fun (j : κ i) => s i j))) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, u4} β (κ i) (fun (j : κ i) => t i j))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u4} α)} {t : forall (i : ι), (κ i) -> (Set.{u3} β)} {f : α -> β}, (forall (i : ι) (j : κ i), Set.SurjOn.{u4, u3} α β f (s i j) (t i j)) -> (Set.SurjOn.{u4, u3} α β f (Set.unionᵢ.{u4, u2} α ι (fun (i : ι) => Set.unionᵢ.{u4, u1} α (κ i) (fun (j : κ i) => s i j))) (Set.unionᵢ.{u3, u2} β ι (fun (i : ι) => Set.unionᵢ.{u3, u1} β (κ i) (fun (j : κ i) => t i j))))
Case conversion may be inaccurate. Consider using '#align set.surj_on_Union₂_Union₂ Set.surjOn_unionᵢ₂_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem surjOn_unionᵢ₂_unionᵢ₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, SurjOn f (s i j) (t i j)) : SurjOn f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  surj_on_Union_Union fun i => surjOn_unionᵢ_unionᵢ (H i)
#align set.surj_on_Union₂_Union₂ Set.surjOn_unionᵢ₂_unionᵢ₂

/- warning: set.surj_on_Inter -> Set.surjOn_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [hi : Nonempty.{u3} ι] {s : ι -> (Set.{u1} α)} {t : Set.{u2} β} {f : α -> β}, (forall (i : ι), Set.SurjOn.{u1, u2} α β f (s i) t) -> (Set.InjOn.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i))) -> (Set.SurjOn.{u1, u2} α β f (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => s i)) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Sort.{u3}} [hi : Nonempty.{u3} ι] {s : ι -> (Set.{u2} α)} {t : Set.{u1} β} {f : α -> β}, (forall (i : ι), Set.SurjOn.{u2, u1} α β f (s i) t) -> (Set.InjOn.{u2, u1} α β f (Set.unionᵢ.{u2, u3} α ι (fun (i : ι) => s i))) -> (Set.SurjOn.{u2, u1} α β f (Set.interᵢ.{u2, u3} α ι (fun (i : ι) => s i)) t)
Case conversion may be inaccurate. Consider using '#align set.surj_on_Inter Set.surjOn_interᵢₓ'. -/
theorem surjOn_interᵢ [hi : Nonempty ι] {s : ι → Set α} {t : Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) t) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) t :=
  by
  intro y hy
  rw [Hinj.image_Inter_eq, mem_Inter]
  exact fun i => H i hy
#align set.surj_on_Inter Set.surjOn_interᵢ

/- warning: set.surj_on_Inter_Inter -> Set.surjOn_interᵢ_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [hi : Nonempty.{u3} ι] {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.SurjOn.{u1, u2} α β f (s i) (t i)) -> (Set.InjOn.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i))) -> (Set.SurjOn.{u1, u2} α β f (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => t i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Sort.{u3}} [hi : Nonempty.{u3} ι] {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u1} β)} {f : α -> β}, (forall (i : ι), Set.SurjOn.{u2, u1} α β f (s i) (t i)) -> (Set.InjOn.{u2, u1} α β f (Set.unionᵢ.{u2, u3} α ι (fun (i : ι) => s i))) -> (Set.SurjOn.{u2, u1} α β f (Set.interᵢ.{u2, u3} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u1, u3} β ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.surj_on_Inter_Inter Set.surjOn_interᵢ_interᵢₓ'. -/
theorem surjOn_interᵢ_interᵢ [hi : Nonempty ι] {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) (⋂ i, t i) :=
  surjOn_interᵢ (fun i => (H i).mono (Subset.refl _) (interᵢ_subset _ _)) Hinj
#align set.surj_on_Inter_Inter Set.surjOn_interᵢ_interᵢ

/-! ### `bij_on` -/


/- warning: set.bij_on_Union -> Set.bijOn_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.BijOn.{u1, u2} α β f (s i) (t i)) -> (Set.InjOn.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i))) -> (Set.BijOn.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => t i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u3} α)} {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.BijOn.{u3, u2} α β f (s i) (t i)) -> (Set.InjOn.{u3, u2} α β f (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i))) -> (Set.BijOn.{u3, u2} α β f (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.bij_on_Union Set.bijOn_unionᵢₓ'. -/
theorem bijOn_unionᵢ {s : ι → Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, BijOn f (s i) (t i))
    (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
  ⟨maps_to_Union_Union fun i => (H i).MapsTo, Hinj, surj_on_Union_Union fun i => (H i).SurjOn⟩
#align set.bij_on_Union Set.bijOn_unionᵢ

/- warning: set.bij_on_Inter -> Set.bijOn_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [hi : Nonempty.{u3} ι] {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.BijOn.{u1, u2} α β f (s i) (t i)) -> (Set.InjOn.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i))) -> (Set.BijOn.{u1, u2} α β f (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => t i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Sort.{u3}} [hi : Nonempty.{u3} ι] {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u1} β)} {f : α -> β}, (forall (i : ι), Set.BijOn.{u2, u1} α β f (s i) (t i)) -> (Set.InjOn.{u2, u1} α β f (Set.unionᵢ.{u2, u3} α ι (fun (i : ι) => s i))) -> (Set.BijOn.{u2, u1} α β f (Set.interᵢ.{u2, u3} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u1, u3} β ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align set.bij_on_Inter Set.bijOn_interᵢₓ'. -/
theorem bijOn_interᵢ [hi : Nonempty ι] {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, BijOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
  ⟨maps_to_Inter_Inter fun i => (H i).MapsTo, hi.elim fun i => (H i).InjOn.mono (interᵢ_subset _ _),
    surjOn_interᵢ_interᵢ (fun i => (H i).SurjOn) Hinj⟩
#align set.bij_on_Inter Set.bijOn_interᵢ

/- warning: set.bij_on_Union_of_directed -> Set.bijOn_unionᵢ_of_directed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {s : ι -> (Set.{u1} α)}, (Directed.{u1, u3} (Set.{u1} α) ι (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α)) s) -> (forall {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.BijOn.{u1, u2} α β f (s i) (t i)) -> (Set.BijOn.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => t i))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {ι : Sort.{u2}} {s : ι -> (Set.{u3} α)}, (Directed.{u3, u2} (Set.{u3} α) ι (fun (x._@.Mathlib.Data.Set.Lattice._hyg.25956 : Set.{u3} α) (x._@.Mathlib.Data.Set.Lattice._hyg.25958 : Set.{u3} α) => HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) x._@.Mathlib.Data.Set.Lattice._hyg.25956 x._@.Mathlib.Data.Set.Lattice._hyg.25958) s) -> (forall {t : ι -> (Set.{u1} β)} {f : α -> β}, (forall (i : ι), Set.BijOn.{u3, u1} α β f (s i) (t i)) -> (Set.BijOn.{u3, u1} α β f (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u1, u2} β ι (fun (i : ι) => t i))))
Case conversion may be inaccurate. Consider using '#align set.bij_on_Union_of_directed Set.bijOn_unionᵢ_of_directedₓ'. -/
theorem bijOn_unionᵢ_of_directed {s : ι → Set α} (hs : Directed (· ⊆ ·) s) {t : ι → Set β}
    {f : α → β} (H : ∀ i, BijOn f (s i) (t i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
  bijOn_unionᵢ H <| inj_on_unionᵢ_of_directed hs fun i => (H i).InjOn
#align set.bij_on_Union_of_directed Set.bijOn_unionᵢ_of_directed

/- warning: set.bij_on_Inter_of_directed -> Set.bijOn_interᵢ_of_directed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : Nonempty.{u3} ι] {s : ι -> (Set.{u1} α)}, (Directed.{u1, u3} (Set.{u1} α) ι (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α)) s) -> (forall {t : ι -> (Set.{u2} β)} {f : α -> β}, (forall (i : ι), Set.BijOn.{u1, u2} α β f (s i) (t i)) -> (Set.BijOn.{u1, u2} α β f (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => t i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Sort.{u3}} [_inst_1 : Nonempty.{u3} ι] {s : ι -> (Set.{u2} α)}, (Directed.{u2, u3} (Set.{u2} α) ι (fun (x._@.Mathlib.Data.Set.Lattice._hyg.26076 : Set.{u2} α) (x._@.Mathlib.Data.Set.Lattice._hyg.26078 : Set.{u2} α) => HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) x._@.Mathlib.Data.Set.Lattice._hyg.26076 x._@.Mathlib.Data.Set.Lattice._hyg.26078) s) -> (forall {t : ι -> (Set.{u1} β)} {f : α -> β}, (forall (i : ι), Set.BijOn.{u2, u1} α β f (s i) (t i)) -> (Set.BijOn.{u2, u1} α β f (Set.interᵢ.{u2, u3} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u1, u3} β ι (fun (i : ι) => t i))))
Case conversion may be inaccurate. Consider using '#align set.bij_on_Inter_of_directed Set.bijOn_interᵢ_of_directedₓ'. -/
theorem bijOn_interᵢ_of_directed [Nonempty ι] {s : ι → Set α} (hs : Directed (· ⊆ ·) s)
    {t : ι → Set β} {f : α → β} (H : ∀ i, BijOn f (s i) (t i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
  bijOn_interᵢ H <| inj_on_unionᵢ_of_directed hs fun i => (H i).InjOn
#align set.bij_on_Inter_of_directed Set.bijOn_interᵢ_of_directed

end Function

/-! ### `image`, `preimage` -/


section Image

/- warning: set.image_Union -> Set.image_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β} {s : ι -> (Set.{u1} α)}, Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i))) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => Set.image.{u1, u2} α β f (s i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} {f : α -> β} {s : ι -> (Set.{u3} α)}, Eq.{succ u2} (Set.{u2} β) (Set.image.{u3, u2} α β f (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i))) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => Set.image.{u3, u2} α β f (s i)))
Case conversion may be inaccurate. Consider using '#align set.image_Union Set.image_unionᵢₓ'. -/
theorem image_unionᵢ {f : α → β} {s : ι → Set α} : (f '' ⋃ i, s i) = ⋃ i, f '' s i :=
  by
  ext1 x
  simp [image, ← exists_and_right, @exists_swap α]
#align set.image_Union Set.image_unionᵢ

/- warning: set.image_Union₂ -> Set.image_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} (f : α -> β) (s : forall (i : ι), (κ i) -> (Set.{u1} α)), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => Set.unionᵢ.{u1, u4} α (κ i) (fun (j : κ i) => s i j)))) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, u4} β (κ i) (fun (j : κ i) => Set.image.{u1, u2} α β f (s i j))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} (f : α -> β) (s : forall (i : ι), (κ i) -> (Set.{u4} α)), Eq.{succ u3} (Set.{u3} β) (Set.image.{u4, u3} α β f (Set.unionᵢ.{u4, u2} α ι (fun (i : ι) => Set.unionᵢ.{u4, u1} α (κ i) (fun (j : κ i) => s i j)))) (Set.unionᵢ.{u3, u2} β ι (fun (i : ι) => Set.unionᵢ.{u3, u1} β (κ i) (fun (j : κ i) => Set.image.{u4, u3} α β f (s i j))))
Case conversion may be inaccurate. Consider using '#align set.image_Union₂ Set.image_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image_unionᵢ₂ (f : α → β) (s : ∀ i, κ i → Set α) :
    (f '' ⋃ (i) (j), s i j) = ⋃ (i) (j), f '' s i j := by simp_rw [image_Union]
#align set.image_Union₂ Set.image_unionᵢ₂

#print Set.univ_subtype /-
theorem univ_subtype {p : α → Prop} : (univ : Set (Subtype p)) = ⋃ (x) (h : p x), {⟨x, h⟩} :=
  Set.ext fun ⟨x, h⟩ => by simp [h]
#align set.univ_subtype Set.univ_subtype
-/

#print Set.range_eq_unionᵢ /-
theorem range_eq_unionᵢ {ι} (f : ι → α) : range f = ⋃ i, {f i} :=
  Set.ext fun a => by simp [@eq_comm α a]
#align set.range_eq_Union Set.range_eq_unionᵢ
-/

/- warning: set.image_eq_Union -> Set.image_eq_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f s) (Set.unionᵢ.{u2, succ u1} β α (fun (i : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) (f i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f s) (Set.unionᵢ.{u1, succ u2} β α (fun (i : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) (f i))))
Case conversion may be inaccurate. Consider using '#align set.image_eq_Union Set.image_eq_unionᵢₓ'. -/
theorem image_eq_unionᵢ (f : α → β) (s : Set α) : f '' s = ⋃ i ∈ s, {f i} :=
  Set.ext fun b => by simp [@eq_comm β b]
#align set.image_eq_Union Set.image_eq_unionᵢ

/- warning: set.bUnion_range -> Set.bunionᵢ_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : ι -> α} {g : α -> (Set.{u2} β)}, Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.range.{u1, u3} α ι f)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.range.{u1, u3} α ι f)) => g x))) (Set.unionᵢ.{u2, u3} β ι (fun (y : ι) => g (f y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} {f : ι -> α} {g : α -> (Set.{u3} β)}, Eq.{succ u3} (Set.{u3} β) (Set.unionᵢ.{u3, succ u2} β α (fun (x : α) => Set.unionᵢ.{u3, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.range.{u2, u1} α ι f)) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.range.{u2, u1} α ι f)) => g x))) (Set.unionᵢ.{u3, u1} β ι (fun (y : ι) => g (f y)))
Case conversion may be inaccurate. Consider using '#align set.bUnion_range Set.bunionᵢ_rangeₓ'. -/
theorem bunionᵢ_range {f : ι → α} {g : α → Set β} : (⋃ x ∈ range f, g x) = ⋃ y, g (f y) :=
  supᵢ_range
#align set.bUnion_range Set.bunionᵢ_range

/- warning: set.Union_Union_eq' -> Set.unionᵢ_unionᵢ_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : ι -> α} {g : α -> (Set.{u2} β)}, Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, u3} β ι (fun (y : ι) => Set.unionᵢ.{u2, 0} β (Eq.{succ u1} α (f y) x) (fun (h : Eq.{succ u1} α (f y) x) => g x)))) (Set.unionᵢ.{u2, u3} β ι (fun (y : ι) => g (f y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} {f : ι -> α} {g : α -> (Set.{u3} β)}, Eq.{succ u3} (Set.{u3} β) (Set.unionᵢ.{u3, succ u2} β α (fun (x : α) => Set.unionᵢ.{u3, u1} β ι (fun (y : ι) => Set.unionᵢ.{u3, 0} β (Eq.{succ u2} α (f y) x) (fun (h : Eq.{succ u2} α (f y) x) => g x)))) (Set.unionᵢ.{u3, u1} β ι (fun (y : ι) => g (f y)))
Case conversion may be inaccurate. Consider using '#align set.Union_Union_eq' Set.unionᵢ_unionᵢ_eq'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
@[simp]
theorem unionᵢ_unionᵢ_eq' {f : ι → α} {g : α → Set β} :
    (⋃ (x) (y) (h : f y = x), g x) = ⋃ y, g (f y) := by simpa using bUnion_range
#align set.Union_Union_eq' Set.unionᵢ_unionᵢ_eq'

/- warning: set.bInter_range -> Set.binterᵢ_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : ι -> α} {g : α -> (Set.{u2} β)}, Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.range.{u1, u3} α ι f)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.range.{u1, u3} α ι f)) => g x))) (Set.interᵢ.{u2, u3} β ι (fun (y : ι) => g (f y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} {f : ι -> α} {g : α -> (Set.{u3} β)}, Eq.{succ u3} (Set.{u3} β) (Set.interᵢ.{u3, succ u2} β α (fun (x : α) => Set.interᵢ.{u3, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.range.{u2, u1} α ι f)) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.range.{u2, u1} α ι f)) => g x))) (Set.interᵢ.{u3, u1} β ι (fun (y : ι) => g (f y)))
Case conversion may be inaccurate. Consider using '#align set.bInter_range Set.binterᵢ_rangeₓ'. -/
theorem binterᵢ_range {f : ι → α} {g : α → Set β} : (⋂ x ∈ range f, g x) = ⋂ y, g (f y) :=
  infᵢ_range
#align set.bInter_range Set.binterᵢ_range

/- warning: set.Inter_Inter_eq' -> Set.interᵢ_interᵢ_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : ι -> α} {g : α -> (Set.{u2} β)}, Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, u3} β ι (fun (y : ι) => Set.interᵢ.{u2, 0} β (Eq.{succ u1} α (f y) x) (fun (h : Eq.{succ u1} α (f y) x) => g x)))) (Set.interᵢ.{u2, u3} β ι (fun (y : ι) => g (f y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} {f : ι -> α} {g : α -> (Set.{u3} β)}, Eq.{succ u3} (Set.{u3} β) (Set.interᵢ.{u3, succ u2} β α (fun (x : α) => Set.interᵢ.{u3, u1} β ι (fun (y : ι) => Set.interᵢ.{u3, 0} β (Eq.{succ u2} α (f y) x) (fun (h : Eq.{succ u2} α (f y) x) => g x)))) (Set.interᵢ.{u3, u1} β ι (fun (y : ι) => g (f y)))
Case conversion may be inaccurate. Consider using '#align set.Inter_Inter_eq' Set.interᵢ_interᵢ_eq'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
@[simp]
theorem interᵢ_interᵢ_eq' {f : ι → α} {g : α → Set β} :
    (⋂ (x) (y) (h : f y = x), g x) = ⋂ y, g (f y) := by simpa using bInter_range
#align set.Inter_Inter_eq' Set.interᵢ_interᵢ_eq'

variable {s : Set γ} {f : γ → α} {g : α → Set β}

/- warning: set.bUnion_image -> Set.bunionᵢ_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u3} γ} {f : γ -> α} {g : α -> (Set.{u2} β)}, Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.image.{u3, u1} γ α f s)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.image.{u3, u1} γ α f s)) => g x))) (Set.unionᵢ.{u2, succ u3} β γ (fun (y : γ) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) y s) (fun (H : Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) y s) => g (f y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} {s : Set.{u1} γ} {f : γ -> α} {g : α -> (Set.{u3} β)}, Eq.{succ u3} (Set.{u3} β) (Set.unionᵢ.{u3, succ u2} β α (fun (x : α) => Set.unionᵢ.{u3, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.image.{u1, u2} γ α f s)) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.image.{u1, u2} γ α f s)) => g x))) (Set.unionᵢ.{u3, succ u1} β γ (fun (y : γ) => Set.unionᵢ.{u3, 0} β (Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) y s) (fun (H : Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) y s) => g (f y))))
Case conversion may be inaccurate. Consider using '#align set.bUnion_image Set.bunionᵢ_imageₓ'. -/
theorem bunionᵢ_image : (⋃ x ∈ f '' s, g x) = ⋃ y ∈ s, g (f y) :=
  supᵢ_image
#align set.bUnion_image Set.bunionᵢ_image

/- warning: set.bInter_image -> Set.binterᵢ_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u3} γ} {f : γ -> α} {g : α -> (Set.{u2} β)}, Eq.{succ u2} (Set.{u2} β) (Set.interᵢ.{u2, succ u1} β α (fun (x : α) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.image.{u3, u1} γ α f s)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.image.{u3, u1} γ α f s)) => g x))) (Set.interᵢ.{u2, succ u3} β γ (fun (y : γ) => Set.interᵢ.{u2, 0} β (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) y s) (fun (H : Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) y s) => g (f y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} {s : Set.{u1} γ} {f : γ -> α} {g : α -> (Set.{u3} β)}, Eq.{succ u3} (Set.{u3} β) (Set.interᵢ.{u3, succ u2} β α (fun (x : α) => Set.interᵢ.{u3, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.image.{u1, u2} γ α f s)) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.image.{u1, u2} γ α f s)) => g x))) (Set.interᵢ.{u3, succ u1} β γ (fun (y : γ) => Set.interᵢ.{u3, 0} β (Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) y s) (fun (H : Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) y s) => g (f y))))
Case conversion may be inaccurate. Consider using '#align set.bInter_image Set.binterᵢ_imageₓ'. -/
theorem binterᵢ_image : (⋂ x ∈ f '' s, g x) = ⋂ y ∈ s, g (f y) :=
  infᵢ_image
#align set.bInter_image Set.binterᵢ_image

end Image

section Preimage

/- warning: set.monotone_preimage -> Set.monotone_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, Monotone.{u2, u1} (Set.{u2} β) (Set.{u1} α) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (Set.preimage.{u1, u2} α β f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, Monotone.{u2, u1} (Set.{u2} β) (Set.{u1} α) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (Set.preimage.{u1, u2} α β f)
Case conversion may be inaccurate. Consider using '#align set.monotone_preimage Set.monotone_preimageₓ'. -/
theorem monotone_preimage {f : α → β} : Monotone (preimage f) := fun a b h => preimage_mono h
#align set.monotone_preimage Set.monotone_preimage

/- warning: set.preimage_Union -> Set.preimage_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β} {s : ι -> (Set.{u2} β)}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => s i))) (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => Set.preimage.{u1, u2} α β f (s i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} {f : α -> β} {s : ι -> (Set.{u3} β)}, Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u3} α β f (Set.unionᵢ.{u3, u1} β ι (fun (i : ι) => s i))) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => Set.preimage.{u2, u3} α β f (s i)))
Case conversion may be inaccurate. Consider using '#align set.preimage_Union Set.preimage_unionᵢₓ'. -/
@[simp]
theorem preimage_unionᵢ {f : α → β} {s : ι → Set β} : (f ⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i :=
  Set.ext <| by simp [preimage]
#align set.preimage_Union Set.preimage_unionᵢ

/- warning: set.preimage_Union₂ -> Set.preimage_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} {f : α -> β} {s : forall (i : ι), (κ i) -> (Set.{u2} β)}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, u4} β (κ i) (fun (j : κ i) => s i j)))) (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => Set.unionᵢ.{u1, u4} α (κ i) (fun (j : κ i) => Set.preimage.{u1, u2} α β f (s i j))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {f : α -> β} {s : forall (i : ι), (κ i) -> (Set.{u4} β)}, Eq.{succ u3} (Set.{u3} α) (Set.preimage.{u3, u4} α β f (Set.unionᵢ.{u4, u2} β ι (fun (i : ι) => Set.unionᵢ.{u4, u1} β (κ i) (fun (j : κ i) => s i j)))) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => Set.preimage.{u3, u4} α β f (s i j))))
Case conversion may be inaccurate. Consider using '#align set.preimage_Union₂ Set.preimage_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem preimage_unionᵢ₂ {f : α → β} {s : ∀ i, κ i → Set β} :
    (f ⁻¹' ⋃ (i) (j), s i j) = ⋃ (i) (j), f ⁻¹' s i j := by simp_rw [preimage_Union]
#align set.preimage_Union₂ Set.preimage_unionᵢ₂

#print Set.preimage_unionₛ /-
@[simp]
theorem preimage_unionₛ {f : α → β} {s : Set (Set β)} : f ⁻¹' ⋃₀ s = ⋃ t ∈ s, f ⁻¹' t := by
  rw [sUnion_eq_bUnion, preimage_Union₂]
#align set.preimage_sUnion Set.preimage_unionₛ
-/

/- warning: set.preimage_Inter -> Set.preimage_interᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β} {s : ι -> (Set.{u2} β)}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => s i))) (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => Set.preimage.{u1, u2} α β f (s i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} {f : α -> β} {s : ι -> (Set.{u3} β)}, Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u3} α β f (Set.interᵢ.{u3, u1} β ι (fun (i : ι) => s i))) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Set.preimage.{u2, u3} α β f (s i)))
Case conversion may be inaccurate. Consider using '#align set.preimage_Inter Set.preimage_interᵢₓ'. -/
theorem preimage_interᵢ {f : α → β} {s : ι → Set β} : (f ⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i := by
  ext <;> simp
#align set.preimage_Inter Set.preimage_interᵢ

/- warning: set.preimage_Inter₂ -> Set.preimage_interᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} {f : α -> β} {s : forall (i : ι), (κ i) -> (Set.{u2} β)}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.interᵢ.{u2, u4} β (κ i) (fun (j : κ i) => s i j)))) (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => Set.interᵢ.{u1, u4} α (κ i) (fun (j : κ i) => Set.preimage.{u1, u2} α β f (s i j))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {f : α -> β} {s : forall (i : ι), (κ i) -> (Set.{u4} β)}, Eq.{succ u3} (Set.{u3} α) (Set.preimage.{u3, u4} α β f (Set.interᵢ.{u4, u2} β ι (fun (i : ι) => Set.interᵢ.{u4, u1} β (κ i) (fun (j : κ i) => s i j)))) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => Set.preimage.{u3, u4} α β f (s i j))))
Case conversion may be inaccurate. Consider using '#align set.preimage_Inter₂ Set.preimage_interᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem preimage_interᵢ₂ {f : α → β} {s : ∀ i, κ i → Set β} :
    (f ⁻¹' ⋂ (i) (j), s i j) = ⋂ (i) (j), f ⁻¹' s i j := by simp_rw [preimage_Inter]
#align set.preimage_Inter₂ Set.preimage_interᵢ₂

#print Set.preimage_interₛ /-
@[simp]
theorem preimage_interₛ {f : α → β} {s : Set (Set β)} : f ⁻¹' ⋂₀ s = ⋂ t ∈ s, f ⁻¹' t := by
  rw [sInter_eq_bInter, preimage_Inter₂]
#align set.preimage_sInter Set.preimage_interₛ
-/

#print Set.bunionᵢ_preimage_singleton /-
@[simp]
theorem bunionᵢ_preimage_singleton (f : α → β) (s : Set β) : (⋃ y ∈ s, f ⁻¹' {y}) = f ⁻¹' s := by
  rw [← preimage_Union₂, bUnion_of_singleton]
#align set.bUnion_preimage_singleton Set.bunionᵢ_preimage_singleton
-/

/- warning: set.bUnion_range_preimage_singleton -> Set.bunionᵢ_range_preimage_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α β (fun (y : β) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (Set.range.{u2, succ u1} β α f)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (Set.range.{u2, succ u1} β α f)) => Set.preimage.{u1, u2} α β f (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) y)))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, succ u1} α β (fun (y : β) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (Set.range.{u1, succ u2} β α f)) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (Set.range.{u1, succ u2} β α f)) => Set.preimage.{u2, u1} α β f (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) y)))) (Set.univ.{u2} α)
Case conversion may be inaccurate. Consider using '#align set.bUnion_range_preimage_singleton Set.bunionᵢ_range_preimage_singletonₓ'. -/
theorem bunionᵢ_range_preimage_singleton (f : α → β) : (⋃ y ∈ range f, f ⁻¹' {y}) = univ := by
  rw [bUnion_preimage_singleton, preimage_range]
#align set.bUnion_range_preimage_singleton Set.bunionᵢ_range_preimage_singleton

end Preimage

section Prod

/- warning: set.prod_Union -> Set.prod_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {s : Set.{u1} α} {t : ι -> (Set.{u2} β)}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => t i))) (Set.unionᵢ.{max u1 u2, u3} (Prod.{u1, u2} α β) ι (fun (i : ι) => Set.prod.{u1, u2} α β s (t i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} {s : Set.{u3} α} {t : ι -> (Set.{u2} β)}, Eq.{max (succ u3) (succ u2)} (Set.{max u2 u3} (Prod.{u3, u2} α β)) (Set.prod.{u3, u2} α β s (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => t i))) (Set.unionᵢ.{max u2 u3, u1} (Prod.{u3, u2} α β) ι (fun (i : ι) => Set.prod.{u3, u2} α β s (t i)))
Case conversion may be inaccurate. Consider using '#align set.prod_Union Set.prod_unionᵢₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_unionᵢ {s : Set α} {t : ι → Set β} : (s ×ˢ ⋃ i, t i) = ⋃ i, s ×ˢ t i :=
  by
  ext
  simp
#align set.prod_Union Set.prod_unionᵢ

/- warning: set.prod_Union₂ -> Set.prod_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} {s : Set.{u1} α} {t : forall (i : ι), (κ i) -> (Set.{u2} β)}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, u4} β (κ i) (fun (j : κ i) => t i j)))) (Set.unionᵢ.{max u1 u2, u3} (Prod.{u1, u2} α β) ι (fun (i : ι) => Set.unionᵢ.{max u1 u2, u4} (Prod.{u1, u2} α β) (κ i) (fun (j : κ i) => Set.prod.{u1, u2} α β s (t i j))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : Set.{u4} α} {t : forall (i : ι), (κ i) -> (Set.{u3} β)}, Eq.{max (succ u4) (succ u3)} (Set.{max u3 u4} (Prod.{u4, u3} α β)) (Set.prod.{u4, u3} α β s (Set.unionᵢ.{u3, u2} β ι (fun (i : ι) => Set.unionᵢ.{u3, u1} β (κ i) (fun (j : κ i) => t i j)))) (Set.unionᵢ.{max u3 u4, u2} (Prod.{u4, u3} α β) ι (fun (i : ι) => Set.unionᵢ.{max u3 u4, u1} (Prod.{u4, u3} α β) (κ i) (fun (j : κ i) => Set.prod.{u4, u3} α β s (t i j))))
Case conversion may be inaccurate. Consider using '#align set.prod_Union₂ Set.prod_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_unionᵢ₂ {s : Set α} {t : ∀ i, κ i → Set β} :
    (s ×ˢ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ×ˢ t i j := by simp_rw [prod_Union]
#align set.prod_Union₂ Set.prod_unionᵢ₂

/- warning: set.prod_sUnion -> Set.prod_unionₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {C : Set.{u2} (Set.{u2} β)}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s (Set.unionₛ.{u2} β C)) (Set.unionₛ.{max u1 u2} (Prod.{u1, u2} α β) (Set.image.{u2, max u1 u2} (Set.{u2} β) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (fun (t : Set.{u2} β) => Set.prod.{u1, u2} α β s t) C))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {C : Set.{u1} (Set.{u1} β)}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s (Set.unionₛ.{u1} β C)) (Set.unionₛ.{max u1 u2} (Prod.{u2, u1} α β) (Set.image.{u1, max u1 u2} (Set.{u1} β) (Set.{max u1 u2} (Prod.{u2, u1} α β)) (fun (t : Set.{u1} β) => Set.prod.{u2, u1} α β s t) C))
Case conversion may be inaccurate. Consider using '#align set.prod_sUnion Set.prod_unionₛₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_unionₛ {s : Set α} {C : Set (Set β)} : s ×ˢ ⋃₀ C = ⋃₀ ((fun t => s ×ˢ t) '' C) := by
  simp_rw [sUnion_eq_bUnion, bUnion_image, prod_Union₂]
#align set.prod_sUnion Set.prod_unionₛ

/- warning: set.Union_prod_const -> Set.unionᵢ_prod_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {s : ι -> (Set.{u1} α)} {t : Set.{u2} β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i)) t) (Set.unionᵢ.{max u1 u2, u3} (Prod.{u1, u2} α β) ι (fun (i : ι) => Set.prod.{u1, u2} α β (s i) t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} {s : ι -> (Set.{u3} α)} {t : Set.{u2} β}, Eq.{max (succ u3) (succ u2)} (Set.{max u2 u3} (Prod.{u3, u2} α β)) (Set.prod.{u3, u2} α β (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i)) t) (Set.unionᵢ.{max u2 u3, u1} (Prod.{u3, u2} α β) ι (fun (i : ι) => Set.prod.{u3, u2} α β (s i) t))
Case conversion may be inaccurate. Consider using '#align set.Union_prod_const Set.unionᵢ_prod_constₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem unionᵢ_prod_const {s : ι → Set α} {t : Set β} : (⋃ i, s i) ×ˢ t = ⋃ i, s i ×ˢ t :=
  by
  ext
  simp
#align set.Union_prod_const Set.unionᵢ_prod_const

/- warning: set.Union₂_prod_const -> Set.unionᵢ₂_prod_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {t : Set.{u2} β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => Set.unionᵢ.{u1, u4} α (κ i) (fun (j : κ i) => s i j))) t) (Set.unionᵢ.{max u1 u2, u3} (Prod.{u1, u2} α β) ι (fun (i : ι) => Set.unionᵢ.{max u1 u2, u4} (Prod.{u1, u2} α β) (κ i) (fun (j : κ i) => Set.prod.{u1, u2} α β (s i j) t)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u4} α)} {t : Set.{u3} β}, Eq.{max (succ u4) (succ u3)} (Set.{max u3 u4} (Prod.{u4, u3} α β)) (Set.prod.{u4, u3} α β (Set.unionᵢ.{u4, u2} α ι (fun (i : ι) => Set.unionᵢ.{u4, u1} α (κ i) (fun (j : κ i) => s i j))) t) (Set.unionᵢ.{max u3 u4, u2} (Prod.{u4, u3} α β) ι (fun (i : ι) => Set.unionᵢ.{max u3 u4, u1} (Prod.{u4, u3} α β) (κ i) (fun (j : κ i) => Set.prod.{u4, u3} α β (s i j) t)))
Case conversion may be inaccurate. Consider using '#align set.Union₂_prod_const Set.unionᵢ₂_prod_constₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem unionᵢ₂_prod_const {s : ∀ i, κ i → Set α} {t : Set β} :
    (⋃ (i) (j), s i j) ×ˢ t = ⋃ (i) (j), s i j ×ˢ t := by simp_rw [Union_prod_const]
#align set.Union₂_prod_const Set.unionᵢ₂_prod_const

/- warning: set.sUnion_prod_const -> Set.unionₛ_prod_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {C : Set.{u1} (Set.{u1} α)} {t : Set.{u2} β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (Set.unionₛ.{u1} α C) t) (Set.unionₛ.{max u1 u2} (Prod.{u1, u2} α β) (Set.image.{u1, max u1 u2} (Set.{u1} α) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (fun (s : Set.{u1} α) => Set.prod.{u1, u2} α β s t) C))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {C : Set.{u2} (Set.{u2} α)} {t : Set.{u1} β}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β (Set.unionₛ.{u2} α C) t) (Set.unionₛ.{max u1 u2} (Prod.{u2, u1} α β) (Set.image.{u2, max u1 u2} (Set.{u2} α) (Set.{max u1 u2} (Prod.{u2, u1} α β)) (fun (s : Set.{u2} α) => Set.prod.{u2, u1} α β s t) C))
Case conversion may be inaccurate. Consider using '#align set.sUnion_prod_const Set.unionₛ_prod_constₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem unionₛ_prod_const {C : Set (Set α)} {t : Set β} :
    ⋃₀ C ×ˢ t = ⋃₀ ((fun s : Set α => s ×ˢ t) '' C) := by
  simp only [sUnion_eq_bUnion, Union₂_prod_const, bUnion_image]
#align set.sUnion_prod_const Set.unionₛ_prod_const

/- warning: set.Union_prod -> Set.unionᵢ_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} (s : ι -> (Set.{u3} α)) (t : ι' -> (Set.{u4} β)), Eq.{succ (max u3 u4)} (Set.{max u3 u4} (Prod.{u3, u4} α β)) (Set.unionᵢ.{max u3 u4, max (succ u1) (succ u2)} (Prod.{u3, u4} α β) (Prod.{u1, u2} ι ι') (fun (x : Prod.{u1, u2} ι ι') => Set.prod.{u3, u4} α β (s (Prod.fst.{u1, u2} ι ι' x)) (t (Prod.snd.{u1, u2} ι ι' x)))) (Set.prod.{u3, u4} α β (Set.unionᵢ.{u3, succ u1} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u4, succ u2} β ι' (fun (i : ι') => t i)))
but is expected to have type
  forall {ι : Type.{u4}} {ι' : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} (s : ι -> (Set.{u2} α)) (t : ι' -> (Set.{u1} β)), Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.unionᵢ.{max u1 u2, max (succ u3) (succ u4)} (Prod.{u2, u1} α β) (Prod.{u4, u3} ι ι') (fun (x : Prod.{u4, u3} ι ι') => Set.prod.{u2, u1} α β (s (Prod.fst.{u4, u3} ι ι' x)) (t (Prod.snd.{u4, u3} ι ι' x)))) (Set.prod.{u2, u1} α β (Set.unionᵢ.{u2, succ u4} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u1, succ u3} β ι' (fun (i : ι') => t i)))
Case conversion may be inaccurate. Consider using '#align set.Union_prod Set.unionᵢ_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem unionᵢ_prod {ι ι' α β} (s : ι → Set α) (t : ι' → Set β) :
    (⋃ x : ι × ι', s x.1 ×ˢ t x.2) = (⋃ i : ι, s i) ×ˢ ⋃ i : ι', t i :=
  by
  ext
  simp
#align set.Union_prod Set.unionᵢ_prod

/- warning: set.Union_prod_of_monotone -> Set.unionᵢ_prod_of_monotone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeSup.{u1} α] {s : α -> (Set.{u2} β)} {t : α -> (Set.{u3} γ)}, (Monotone.{u1, u2} α (Set.{u2} β) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) s) -> (Monotone.{u1, u3} α (Set.{u3} γ) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) (PartialOrder.toPreorder.{u3} (Set.{u3} γ) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} γ) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} γ) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} γ) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} γ) (Set.completeBooleanAlgebra.{u3} γ))))))) t) -> (Eq.{succ (max u2 u3)} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.unionᵢ.{max u2 u3, succ u1} (Prod.{u2, u3} β γ) α (fun (x : α) => Set.prod.{u2, u3} β γ (s x) (t x))) (Set.prod.{u2, u3} β γ (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => s x)) (Set.unionᵢ.{u3, succ u1} γ α (fun (x : α) => t x))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : SemilatticeSup.{u3} α] {s : α -> (Set.{u2} β)} {t : α -> (Set.{u1} γ)}, (Monotone.{u3, u2} α (Set.{u2} β) (PartialOrder.toPreorder.{u3} α (SemilatticeSup.toPartialOrder.{u3} α _inst_1)) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))))) s) -> (Monotone.{u3, u1} α (Set.{u1} γ) (PartialOrder.toPreorder.{u3} α (SemilatticeSup.toPartialOrder.{u3} α _inst_1)) (PartialOrder.toPreorder.{u1} (Set.{u1} γ) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} γ) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} γ) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} γ) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} γ) (Set.instCompleteBooleanAlgebraSet.{u1} γ))))))) t) -> (Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (Set.unionᵢ.{max u1 u2, succ u3} (Prod.{u2, u1} β γ) α (fun (x : α) => Set.prod.{u2, u1} β γ (s x) (t x))) (Set.prod.{u2, u1} β γ (Set.unionᵢ.{u2, succ u3} β α (fun (x : α) => s x)) (Set.unionᵢ.{u1, succ u3} γ α (fun (x : α) => t x))))
Case conversion may be inaccurate. Consider using '#align set.Union_prod_of_monotone Set.unionᵢ_prod_of_monotoneₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem unionᵢ_prod_of_monotone [SemilatticeSup α] {s : α → Set β} {t : α → Set γ} (hs : Monotone s)
    (ht : Monotone t) : (⋃ x, s x ×ˢ t x) = (⋃ x, s x) ×ˢ ⋃ x, t x :=
  by
  ext ⟨z, w⟩; simp only [mem_prod, mem_Union, exists_imp, and_imp, iff_def]; constructor
  · intro x hz hw
    exact ⟨⟨x, hz⟩, x, hw⟩
  · intro x hz x' hw
    exact ⟨x ⊔ x', hs le_sup_left hz, ht le_sup_right hw⟩
#align set.Union_prod_of_monotone Set.unionᵢ_prod_of_monotone

/- warning: set.sInter_prod_sInter_subset -> Set.interₛ_prod_interₛ_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (S : Set.{u1} (Set.{u1} α)) (T : Set.{u2} (Set.{u2} β)), HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasSubset.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (Set.interₛ.{u1} α S) (Set.interₛ.{u2} β T)) (Set.interᵢ.{max u1 u2, succ (max u1 u2)} (Prod.{u1, u2} α β) (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β)) (fun (r : Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β)) => Set.interᵢ.{max u1 u2, 0} (Prod.{u1, u2} α β) (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β)) (Set.{max u1 u2} (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β))) (Set.hasMem.{max u1 u2} (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β))) r (Set.prod.{u1, u2} (Set.{u1} α) (Set.{u2} β) S T)) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β)) (Set.{max u1 u2} (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β))) (Set.hasMem.{max u1 u2} (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β))) r (Set.prod.{u1, u2} (Set.{u1} α) (Set.{u2} β) S T)) => Set.prod.{u1, u2} α β (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) r) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) r))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (S : Set.{u2} (Set.{u2} α)) (T : Set.{u1} (Set.{u1} β)), HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instHasSubsetSet.{max u2 u1} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β (Set.interₛ.{u2} α S) (Set.interₛ.{u1} β T)) (Set.interᵢ.{max u2 u1, succ (max u2 u1)} (Prod.{u2, u1} α β) (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β)) (fun (r : Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β)) => Set.interᵢ.{max u2 u1, 0} (Prod.{u2, u1} α β) (Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β)) (Set.{max u1 u2} (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β))) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β))) r (Set.prod.{u2, u1} (Set.{u2} α) (Set.{u1} β) S T)) (fun (H : Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β)) (Set.{max u1 u2} (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β))) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β))) r (Set.prod.{u2, u1} (Set.{u2} α) (Set.{u1} β) S T)) => Set.prod.{u2, u1} α β (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) r) (Prod.snd.{u2, u1} (Set.{u2} α) (Set.{u1} β) r))))
Case conversion may be inaccurate. Consider using '#align set.sInter_prod_sInter_subset Set.interₛ_prod_interₛ_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem interₛ_prod_interₛ_subset (S : Set (Set α)) (T : Set (Set β)) :
    ⋂₀ S ×ˢ ⋂₀ T ⊆ ⋂ r ∈ S ×ˢ T, r.1 ×ˢ r.2 :=
  subset_interᵢ₂ fun x hx y hy => ⟨hy.1 x.1 hx.1, hy.2 x.2 hx.2⟩
#align set.sInter_prod_sInter_subset Set.interₛ_prod_interₛ_subset

/- warning: set.sInter_prod_sInter -> Set.interₛ_prod_interₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {S : Set.{u1} (Set.{u1} α)} {T : Set.{u2} (Set.{u2} β)}, (Set.Nonempty.{u1} (Set.{u1} α) S) -> (Set.Nonempty.{u2} (Set.{u2} β) T) -> (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (Set.interₛ.{u1} α S) (Set.interₛ.{u2} β T)) (Set.interᵢ.{max u1 u2, succ (max u1 u2)} (Prod.{u1, u2} α β) (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β)) (fun (r : Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β)) => Set.interᵢ.{max u1 u2, 0} (Prod.{u1, u2} α β) (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β)) (Set.{max u1 u2} (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β))) (Set.hasMem.{max u1 u2} (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β))) r (Set.prod.{u1, u2} (Set.{u1} α) (Set.{u2} β) S T)) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β)) (Set.{max u1 u2} (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β))) (Set.hasMem.{max u1 u2} (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β))) r (Set.prod.{u1, u2} (Set.{u1} α) (Set.{u2} β) S T)) => Set.prod.{u1, u2} α β (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) r) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) r)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {S : Set.{u2} (Set.{u2} α)} {T : Set.{u1} (Set.{u1} β)}, (Set.Nonempty.{u2} (Set.{u2} α) S) -> (Set.Nonempty.{u1} (Set.{u1} β) T) -> (Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β (Set.interₛ.{u2} α S) (Set.interₛ.{u1} β T)) (Set.interᵢ.{max u1 u2, succ (max u2 u1)} (Prod.{u2, u1} α β) (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β)) (fun (r : Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β)) => Set.interᵢ.{max u1 u2, 0} (Prod.{u2, u1} α β) (Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β)) (Set.{max u1 u2} (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β))) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β))) r (Set.prod.{u2, u1} (Set.{u2} α) (Set.{u1} β) S T)) (fun (H : Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β)) (Set.{max u1 u2} (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β))) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β))) r (Set.prod.{u2, u1} (Set.{u2} α) (Set.{u1} β) S T)) => Set.prod.{u2, u1} α β (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) r) (Prod.snd.{u2, u1} (Set.{u2} α) (Set.{u1} β) r)))))
Case conversion may be inaccurate. Consider using '#align set.sInter_prod_sInter Set.interₛ_prod_interₛₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem interₛ_prod_interₛ {S : Set (Set α)} {T : Set (Set β)} (hS : S.Nonempty) (hT : T.Nonempty) :
    ⋂₀ S ×ˢ ⋂₀ T = ⋂ r ∈ S ×ˢ T, r.1 ×ˢ r.2 :=
  by
  obtain ⟨s₁, h₁⟩ := hS
  obtain ⟨s₂, h₂⟩ := hT
  refine' Set.Subset.antisymm (sInter_prod_sInter_subset S T) fun x hx => _
  rw [mem_Inter₂] at hx
  exact ⟨fun s₀ h₀ => (hx (s₀, s₂) ⟨h₀, h₂⟩).1, fun s₀ h₀ => (hx (s₁, s₀) ⟨h₁, h₀⟩).2⟩
#align set.sInter_prod_sInter Set.interₛ_prod_interₛ

/- warning: set.sInter_prod -> Set.interₛ_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {S : Set.{u1} (Set.{u1} α)}, (Set.Nonempty.{u1} (Set.{u1} α) S) -> (forall (t : Set.{u2} β), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (Set.interₛ.{u1} α S) t) (Set.interᵢ.{max u1 u2, succ u1} (Prod.{u1, u2} α β) (Set.{u1} α) (fun (s : Set.{u1} α) => Set.interᵢ.{max u1 u2, 0} (Prod.{u1, u2} α β) (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s S) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s S) => Set.prod.{u1, u2} α β s t))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {S : Set.{u2} (Set.{u2} α)}, (Set.Nonempty.{u2} (Set.{u2} α) S) -> (forall (t : Set.{u1} β), Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β (Set.interₛ.{u2} α S) t) (Set.interᵢ.{max u1 u2, succ u2} (Prod.{u2, u1} α β) (Set.{u2} α) (fun (s : Set.{u2} α) => Set.interᵢ.{max u1 u2, 0} (Prod.{u2, u1} α β) (Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) s S) (fun (H : Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) s S) => Set.prod.{u2, u1} α β s t))))
Case conversion may be inaccurate. Consider using '#align set.sInter_prod Set.interₛ_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem interₛ_prod {S : Set (Set α)} (hS : S.Nonempty) (t : Set β) : ⋂₀ S ×ˢ t = ⋂ s ∈ S, s ×ˢ t :=
  by
  rw [← sInter_singleton t, sInter_prod_sInter hS (singleton_nonempty t), sInter_singleton]
  simp_rw [prod_singleton, mem_image, Inter_exists, bInter_and', Inter_Inter_eq_right]
#align set.sInter_prod Set.interₛ_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.prod_interₛ /-
theorem prod_interₛ {T : Set (Set β)} (hT : T.Nonempty) (s : Set α) : s ×ˢ ⋂₀ T = ⋂ t ∈ T, s ×ˢ t :=
  by
  rw [← sInter_singleton s, sInter_prod_sInter (singleton_nonempty s) hT, sInter_singleton]
  simp_rw [singleton_prod, mem_image, Inter_exists, bInter_and', Inter_Inter_eq_right]
#align set.prod_sInter Set.prod_interₛ
-/

end Prod

section Image2

variable (f : α → β → γ) {s : Set α} {t : Set β}

/- warning: set.Union_image_left -> Set.unionᵢ_image_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) {s : Set.{u1} α} {t : Set.{u2} β}, Eq.{succ u3} (Set.{u3} γ) (Set.unionᵢ.{u3, succ u1} γ α (fun (a : α) => Set.unionᵢ.{u3, 0} γ (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Set.image.{u2, u3} β γ (f a) t))) (Set.image2.{u1, u2, u3} α β γ f s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} (f : α -> β -> γ) {s : Set.{u2} α} {t : Set.{u1} β}, Eq.{succ u3} (Set.{u3} γ) (Set.unionᵢ.{u3, succ u2} γ α (fun (a : α) => Set.unionᵢ.{u3, 0} γ (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) => Set.image.{u1, u3} β γ (f a) t))) (Set.image2.{u2, u1, u3} α β γ f s t)
Case conversion may be inaccurate. Consider using '#align set.Union_image_left Set.unionᵢ_image_leftₓ'. -/
theorem unionᵢ_image_left : (⋃ a ∈ s, f a '' t) = image2 f s t :=
  by
  ext y
  constructor <;> simp only [mem_Union] <;> rintro ⟨a, ha, x, hx, ax⟩ <;> exact ⟨a, x, ha, hx, ax⟩
#align set.Union_image_left Set.unionᵢ_image_left

#print Set.unionᵢ_image_right /-
theorem unionᵢ_image_right : (⋃ b ∈ t, (fun a => f a b) '' s) = image2 f s t :=
  by
  ext y
  constructor <;> simp only [mem_Union] <;> rintro ⟨a, b, c, d, e⟩
  exact ⟨c, a, d, b, e⟩
  exact ⟨b, d, a, c, e⟩
#align set.Union_image_right Set.unionᵢ_image_right
-/

/- warning: set.image2_Union_left -> Set.image2_unionᵢ_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {ι : Sort.{u4}} (f : α -> β -> γ) (s : ι -> (Set.{u1} α)) (t : Set.{u2} β), Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f (Set.unionᵢ.{u1, u4} α ι (fun (i : ι) => s i)) t) (Set.unionᵢ.{u3, u4} γ ι (fun (i : ι) => Set.image2.{u1, u2, u3} α β γ f (s i) t))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {ι : Sort.{u1}} (f : α -> β -> γ) (s : ι -> (Set.{u4} α)) (t : Set.{u3} β), Eq.{succ u2} (Set.{u2} γ) (Set.image2.{u4, u3, u2} α β γ f (Set.unionᵢ.{u4, u1} α ι (fun (i : ι) => s i)) t) (Set.unionᵢ.{u2, u1} γ ι (fun (i : ι) => Set.image2.{u4, u3, u2} α β γ f (s i) t))
Case conversion may be inaccurate. Consider using '#align set.image2_Union_left Set.image2_unionᵢ_leftₓ'. -/
theorem image2_unionᵢ_left (s : ι → Set α) (t : Set β) :
    image2 f (⋃ i, s i) t = ⋃ i, image2 f (s i) t := by
  simp only [← image_prod, Union_prod_const, image_Union]
#align set.image2_Union_left Set.image2_unionᵢ_left

/- warning: set.image2_Union_right -> Set.image2_unionᵢ_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {ι : Sort.{u4}} (f : α -> β -> γ) (s : Set.{u1} α) (t : ι -> (Set.{u2} β)), Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s (Set.unionᵢ.{u2, u4} β ι (fun (i : ι) => t i))) (Set.unionᵢ.{u3, u4} γ ι (fun (i : ι) => Set.image2.{u1, u2, u3} α β γ f s (t i)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {ι : Sort.{u1}} (f : α -> β -> γ) (s : Set.{u4} α) (t : ι -> (Set.{u3} β)), Eq.{succ u2} (Set.{u2} γ) (Set.image2.{u4, u3, u2} α β γ f s (Set.unionᵢ.{u3, u1} β ι (fun (i : ι) => t i))) (Set.unionᵢ.{u2, u1} γ ι (fun (i : ι) => Set.image2.{u4, u3, u2} α β γ f s (t i)))
Case conversion may be inaccurate. Consider using '#align set.image2_Union_right Set.image2_unionᵢ_rightₓ'. -/
theorem image2_unionᵢ_right (s : Set α) (t : ι → Set β) :
    image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i) := by
  simp only [← image_prod, prod_Union, image_Union]
#align set.image2_Union_right Set.image2_unionᵢ_right

/- warning: set.image2_Union₂_left -> Set.image2_unionᵢ₂_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {ι : Sort.{u4}} {κ : ι -> Sort.{u5}} (f : α -> β -> γ) (s : forall (i : ι), (κ i) -> (Set.{u1} α)) (t : Set.{u2} β), Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f (Set.unionᵢ.{u1, u4} α ι (fun (i : ι) => Set.unionᵢ.{u1, u5} α (κ i) (fun (j : κ i) => s i j))) t) (Set.unionᵢ.{u3, u4} γ ι (fun (i : ι) => Set.unionᵢ.{u3, u5} γ (κ i) (fun (j : κ i) => Set.image2.{u1, u2, u3} α β γ f (s i j) t)))
but is expected to have type
  forall {α : Type.{u5}} {β : Type.{u4}} {γ : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} (f : α -> β -> γ) (s : forall (i : ι), (κ i) -> (Set.{u5} α)) (t : Set.{u4} β), Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u5, u4, u3} α β γ f (Set.unionᵢ.{u5, u2} α ι (fun (i : ι) => Set.unionᵢ.{u5, u1} α (κ i) (fun (j : κ i) => s i j))) t) (Set.unionᵢ.{u3, u2} γ ι (fun (i : ι) => Set.unionᵢ.{u3, u1} γ (κ i) (fun (j : κ i) => Set.image2.{u5, u4, u3} α β γ f (s i j) t)))
Case conversion may be inaccurate. Consider using '#align set.image2_Union₂_left Set.image2_unionᵢ₂_leftₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_unionᵢ₂_left (s : ∀ i, κ i → Set α) (t : Set β) :
    image2 f (⋃ (i) (j), s i j) t = ⋃ (i) (j), image2 f (s i j) t := by simp_rw [image2_Union_left]
#align set.image2_Union₂_left Set.image2_unionᵢ₂_left

/- warning: set.image2_Union₂_right -> Set.image2_unionᵢ₂_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {ι : Sort.{u4}} {κ : ι -> Sort.{u5}} (f : α -> β -> γ) (s : Set.{u1} α) (t : forall (i : ι), (κ i) -> (Set.{u2} β)), Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s (Set.unionᵢ.{u2, u4} β ι (fun (i : ι) => Set.unionᵢ.{u2, u5} β (κ i) (fun (j : κ i) => t i j)))) (Set.unionᵢ.{u3, u4} γ ι (fun (i : ι) => Set.unionᵢ.{u3, u5} γ (κ i) (fun (j : κ i) => Set.image2.{u1, u2, u3} α β γ f s (t i j))))
but is expected to have type
  forall {α : Type.{u5}} {β : Type.{u4}} {γ : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} (f : α -> β -> γ) (s : Set.{u5} α) (t : forall (i : ι), (κ i) -> (Set.{u4} β)), Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u5, u4, u3} α β γ f s (Set.unionᵢ.{u4, u2} β ι (fun (i : ι) => Set.unionᵢ.{u4, u1} β (κ i) (fun (j : κ i) => t i j)))) (Set.unionᵢ.{u3, u2} γ ι (fun (i : ι) => Set.unionᵢ.{u3, u1} γ (κ i) (fun (j : κ i) => Set.image2.{u5, u4, u3} α β γ f s (t i j))))
Case conversion may be inaccurate. Consider using '#align set.image2_Union₂_right Set.image2_unionᵢ₂_rightₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_unionᵢ₂_right (s : Set α) (t : ∀ i, κ i → Set β) :
    image2 f s (⋃ (i) (j), t i j) = ⋃ (i) (j), image2 f s (t i j) := by simp_rw [image2_Union_right]
#align set.image2_Union₂_right Set.image2_unionᵢ₂_right

/- warning: set.image2_Inter_subset_left -> Set.image2_interᵢ_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {ι : Sort.{u4}} (f : α -> β -> γ) (s : ι -> (Set.{u1} α)) (t : Set.{u2} β), HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f (Set.interᵢ.{u1, u4} α ι (fun (i : ι) => s i)) t) (Set.interᵢ.{u3, u4} γ ι (fun (i : ι) => Set.image2.{u1, u2, u3} α β γ f (s i) t))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {ι : Sort.{u1}} (f : α -> β -> γ) (s : ι -> (Set.{u4} α)) (t : Set.{u3} β), HasSubset.Subset.{u2} (Set.{u2} γ) (Set.instHasSubsetSet.{u2} γ) (Set.image2.{u4, u3, u2} α β γ f (Set.interᵢ.{u4, u1} α ι (fun (i : ι) => s i)) t) (Set.interᵢ.{u2, u1} γ ι (fun (i : ι) => Set.image2.{u4, u3, u2} α β γ f (s i) t))
Case conversion may be inaccurate. Consider using '#align set.image2_Inter_subset_left Set.image2_interᵢ_subset_leftₓ'. -/
theorem image2_interᵢ_subset_left (s : ι → Set α) (t : Set β) :
    image2 f (⋂ i, s i) t ⊆ ⋂ i, image2 f (s i) t :=
  by
  simp_rw [image2_subset_iff, mem_Inter]
  exact fun x hx y hy i => mem_image2_of_mem (hx _) hy
#align set.image2_Inter_subset_left Set.image2_interᵢ_subset_left

/- warning: set.image2_Inter_subset_right -> Set.image2_interᵢ_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {ι : Sort.{u4}} (f : α -> β -> γ) (s : Set.{u1} α) (t : ι -> (Set.{u2} β)), HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s (Set.interᵢ.{u2, u4} β ι (fun (i : ι) => t i))) (Set.interᵢ.{u3, u4} γ ι (fun (i : ι) => Set.image2.{u1, u2, u3} α β γ f s (t i)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {ι : Sort.{u1}} (f : α -> β -> γ) (s : Set.{u4} α) (t : ι -> (Set.{u3} β)), HasSubset.Subset.{u2} (Set.{u2} γ) (Set.instHasSubsetSet.{u2} γ) (Set.image2.{u4, u3, u2} α β γ f s (Set.interᵢ.{u3, u1} β ι (fun (i : ι) => t i))) (Set.interᵢ.{u2, u1} γ ι (fun (i : ι) => Set.image2.{u4, u3, u2} α β γ f s (t i)))
Case conversion may be inaccurate. Consider using '#align set.image2_Inter_subset_right Set.image2_interᵢ_subset_rightₓ'. -/
theorem image2_interᵢ_subset_right (s : Set α) (t : ι → Set β) :
    image2 f s (⋂ i, t i) ⊆ ⋂ i, image2 f s (t i) :=
  by
  simp_rw [image2_subset_iff, mem_Inter]
  exact fun x hx y hy i => mem_image2_of_mem hx (hy _)
#align set.image2_Inter_subset_right Set.image2_interᵢ_subset_right

/- warning: set.image2_Inter₂_subset_left -> Set.image2_interᵢ₂_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {ι : Sort.{u4}} {κ : ι -> Sort.{u5}} (f : α -> β -> γ) (s : forall (i : ι), (κ i) -> (Set.{u1} α)) (t : Set.{u2} β), HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f (Set.interᵢ.{u1, u4} α ι (fun (i : ι) => Set.interᵢ.{u1, u5} α (κ i) (fun (j : κ i) => s i j))) t) (Set.interᵢ.{u3, u4} γ ι (fun (i : ι) => Set.interᵢ.{u3, u5} γ (κ i) (fun (j : κ i) => Set.image2.{u1, u2, u3} α β γ f (s i j) t)))
but is expected to have type
  forall {α : Type.{u5}} {β : Type.{u4}} {γ : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} (f : α -> β -> γ) (s : forall (i : ι), (κ i) -> (Set.{u5} α)) (t : Set.{u4} β), HasSubset.Subset.{u3} (Set.{u3} γ) (Set.instHasSubsetSet.{u3} γ) (Set.image2.{u5, u4, u3} α β γ f (Set.interᵢ.{u5, u2} α ι (fun (i : ι) => Set.interᵢ.{u5, u1} α (κ i) (fun (j : κ i) => s i j))) t) (Set.interᵢ.{u3, u2} γ ι (fun (i : ι) => Set.interᵢ.{u3, u1} γ (κ i) (fun (j : κ i) => Set.image2.{u5, u4, u3} α β γ f (s i j) t)))
Case conversion may be inaccurate. Consider using '#align set.image2_Inter₂_subset_left Set.image2_interᵢ₂_subset_leftₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_interᵢ₂_subset_left (s : ∀ i, κ i → Set α) (t : Set β) :
    image2 f (⋂ (i) (j), s i j) t ⊆ ⋂ (i) (j), image2 f (s i j) t :=
  by
  simp_rw [image2_subset_iff, mem_Inter]
  exact fun x hx y hy i j => mem_image2_of_mem (hx _ _) hy
#align set.image2_Inter₂_subset_left Set.image2_interᵢ₂_subset_left

/- warning: set.image2_Inter₂_subset_right -> Set.image2_interᵢ₂_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {ι : Sort.{u4}} {κ : ι -> Sort.{u5}} (f : α -> β -> γ) (s : Set.{u1} α) (t : forall (i : ι), (κ i) -> (Set.{u2} β)), HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s (Set.interᵢ.{u2, u4} β ι (fun (i : ι) => Set.interᵢ.{u2, u5} β (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u3, u4} γ ι (fun (i : ι) => Set.interᵢ.{u3, u5} γ (κ i) (fun (j : κ i) => Set.image2.{u1, u2, u3} α β γ f s (t i j))))
but is expected to have type
  forall {α : Type.{u5}} {β : Type.{u4}} {γ : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} (f : α -> β -> γ) (s : Set.{u5} α) (t : forall (i : ι), (κ i) -> (Set.{u4} β)), HasSubset.Subset.{u3} (Set.{u3} γ) (Set.instHasSubsetSet.{u3} γ) (Set.image2.{u5, u4, u3} α β γ f s (Set.interᵢ.{u4, u2} β ι (fun (i : ι) => Set.interᵢ.{u4, u1} β (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u3, u2} γ ι (fun (i : ι) => Set.interᵢ.{u3, u1} γ (κ i) (fun (j : κ i) => Set.image2.{u5, u4, u3} α β γ f s (t i j))))
Case conversion may be inaccurate. Consider using '#align set.image2_Inter₂_subset_right Set.image2_interᵢ₂_subset_rightₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_interᵢ₂_subset_right (s : Set α) (t : ∀ i, κ i → Set β) :
    image2 f s (⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), image2 f s (t i j) :=
  by
  simp_rw [image2_subset_iff, mem_Inter]
  exact fun x hx y hy i j => mem_image2_of_mem hx (hy _ _)
#align set.image2_Inter₂_subset_right Set.image2_interᵢ₂_subset_right

/- warning: set.image2_eq_Union -> Set.image2_eq_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (Set.unionᵢ.{u3, succ u1} γ α (fun (i : α) => Set.unionᵢ.{u3, 0} γ (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => Set.unionᵢ.{u3, succ u2} γ β (fun (j : β) => Set.unionᵢ.{u3, 0} γ (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) j t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) j t) => Singleton.singleton.{u3, u3} γ (Set.{u3} γ) (Set.hasSingleton.{u3} γ) (f i j))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (s : Set.{u3} α) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} γ) (Set.image2.{u3, u2, u1} α β γ f s t) (Set.unionᵢ.{u1, succ u3} γ α (fun (i : α) => Set.unionᵢ.{u1, 0} γ (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) i s) (fun (H : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) i s) => Set.unionᵢ.{u1, succ u2} γ β (fun (j : β) => Set.unionᵢ.{u1, 0} γ (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) j t) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) j t) => Singleton.singleton.{u1, u1} γ (Set.{u1} γ) (Set.instSingletonSet.{u1} γ) (f i j))))))
Case conversion may be inaccurate. Consider using '#align set.image2_eq_Union Set.image2_eq_unionᵢₓ'. -/
/-- The `set.image2` version of `set.image_eq_Union` -/
theorem image2_eq_unionᵢ (s : Set α) (t : Set β) : image2 f s t = ⋃ (i ∈ s) (j ∈ t), {f i j} := by
  simp_rw [← image_eq_Union, Union_image_left]
#align set.image2_eq_Union Set.image2_eq_unionᵢ

/- warning: set.prod_eq_bUnion_left -> Set.prod_eq_bunionᵢ_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t) (Set.unionᵢ.{max u1 u2, succ u1} (Prod.{u1, u2} α β) α (fun (a : α) => Set.unionᵢ.{max u1 u2, 0} (Prod.{u1, u2} α β) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Set.image.{u2, max u1 u2} β (Prod.{u1, u2} α β) (fun (b : β) => Prod.mk.{u1, u2} α β a b) t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s t) (Set.unionᵢ.{max u1 u2, succ u2} (Prod.{u2, u1} α β) α (fun (a : α) => Set.unionᵢ.{max u1 u2, 0} (Prod.{u2, u1} α β) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) => Set.image.{u1, max u1 u2} β (Prod.{u2, u1} α β) (fun (b : β) => Prod.mk.{u2, u1} α β a b) t)))
Case conversion may be inaccurate. Consider using '#align set.prod_eq_bUnion_left Set.prod_eq_bunionᵢ_leftₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_eq_bunionᵢ_left : s ×ˢ t = ⋃ a ∈ s, (fun b => (a, b)) '' t := by
  rw [Union_image_left, image2_mk_eq_prod]
#align set.prod_eq_bUnion_left Set.prod_eq_bunionᵢ_left

/- warning: set.prod_eq_bUnion_right -> Set.prod_eq_bunionᵢ_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t) (Set.unionᵢ.{max u1 u2, succ u2} (Prod.{u1, u2} α β) β (fun (b : β) => Set.unionᵢ.{max u1 u2, 0} (Prod.{u1, u2} α β) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) => Set.image.{u1, max u1 u2} α (Prod.{u1, u2} α β) (fun (a : α) => Prod.mk.{u1, u2} α β a b) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s t) (Set.unionᵢ.{max u1 u2, succ u1} (Prod.{u2, u1} α β) β (fun (b : β) => Set.unionᵢ.{max u1 u2, 0} (Prod.{u2, u1} α β) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b t) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b t) => Set.image.{u2, max u1 u2} α (Prod.{u2, u1} α β) (fun (a : α) => Prod.mk.{u2, u1} α β a b) s)))
Case conversion may be inaccurate. Consider using '#align set.prod_eq_bUnion_right Set.prod_eq_bunionᵢ_rightₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_eq_bunionᵢ_right : s ×ˢ t = ⋃ b ∈ t, (fun a => (a, b)) '' s := by
  rw [Union_image_right, image2_mk_eq_prod]
#align set.prod_eq_bUnion_right Set.prod_eq_bunionᵢ_right

end Image2

section Seq

#print Set.seq /-
/-- Given a set `s` of functions `α → β` and `t : set α`, `seq s t` is the union of `f '' t` over
all `f ∈ s`. -/
def seq (s : Set (α → β)) (t : Set α) : Set β :=
  { b | ∃ f ∈ s, ∃ a ∈ t, (f : α → β) a = b }
#align set.seq Set.seq
-/

/- warning: set.seq_def -> Set.seq_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{max u1 u2} (α -> β)} {t : Set.{u1} α}, Eq.{succ u2} (Set.{u2} β) (Set.seq.{u1, u2} α β s t) (Set.unionᵢ.{u2, succ (max u1 u2)} β (α -> β) (fun (f : α -> β) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{max u1 u2, max u1 u2} (α -> β) (Set.{max u1 u2} (α -> β)) (Set.hasMem.{max u1 u2} (α -> β)) f s) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (α -> β) (Set.{max u1 u2} (α -> β)) (Set.hasMem.{max u1 u2} (α -> β)) f s) => Set.image.{u1, u2} α β f t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{max u2 u1} (α -> β)} {t : Set.{u2} α}, Eq.{succ u1} (Set.{u1} β) (Set.seq.{u2, u1} α β s t) (Set.unionᵢ.{u1, succ (max u2 u1)} β (α -> β) (fun (f : α -> β) => Set.unionᵢ.{u1, 0} β (Membership.mem.{max u2 u1, max u2 u1} (α -> β) (Set.{max u2 u1} (α -> β)) (Set.instMembershipSet.{max u2 u1} (α -> β)) f s) (fun (H : Membership.mem.{max u2 u1, max u2 u1} (α -> β) (Set.{max u2 u1} (α -> β)) (Set.instMembershipSet.{max u2 u1} (α -> β)) f s) => Set.image.{u2, u1} α β f t)))
Case conversion may be inaccurate. Consider using '#align set.seq_def Set.seq_defₓ'. -/
theorem seq_def {s : Set (α → β)} {t : Set α} : seq s t = ⋃ f ∈ s, f '' t :=
  Set.ext <| by simp [seq]
#align set.seq_def Set.seq_def

/- warning: set.mem_seq_iff -> Set.mem_seq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{max u1 u2} (α -> β)} {t : Set.{u1} α} {b : β}, Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.seq.{u1, u2} α β s t)) (Exists.{succ (max u1 u2)} (α -> β) (fun (f : α -> β) => Exists.{0} (Membership.Mem.{max u1 u2, max u1 u2} (α -> β) (Set.{max u1 u2} (α -> β)) (Set.hasMem.{max u1 u2} (α -> β)) f s) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (α -> β) (Set.{max u1 u2} (α -> β)) (Set.hasMem.{max u1 u2} (α -> β)) f s) => Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) => Eq.{succ u2} β (f a) b)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{max u2 u1} (α -> β)} {t : Set.{u2} α} {b : β}, Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b (Set.seq.{u2, u1} α β s t)) (Exists.{succ (max u2 u1)} (α -> β) (fun (f : α -> β) => And (Membership.mem.{max u2 u1, max u2 u1} (α -> β) (Set.{max u2 u1} (α -> β)) (Set.instMembershipSet.{max u2 u1} (α -> β)) f s) (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a t) (Eq.{succ u1} β (f a) b)))))
Case conversion may be inaccurate. Consider using '#align set.mem_seq_iff Set.mem_seq_iffₓ'. -/
@[simp]
theorem mem_seq_iff {s : Set (α → β)} {t : Set α} {b : β} :
    b ∈ seq s t ↔ ∃ f ∈ s, ∃ a ∈ t, (f : α → β) a = b :=
  Iff.rfl
#align set.mem_seq_iff Set.mem_seq_iff

/- warning: set.seq_subset -> Set.seq_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{max u1 u2} (α -> β)} {t : Set.{u1} α} {u : Set.{u2} β}, Iff (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.seq.{u1, u2} α β s t) u) (forall (f : α -> β), (Membership.Mem.{max u1 u2, max u1 u2} (α -> β) (Set.{max u1 u2} (α -> β)) (Set.hasMem.{max u1 u2} (α -> β)) f s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f a) u)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{max u2 u1} (α -> β)} {t : Set.{u2} α} {u : Set.{u1} β}, Iff (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.seq.{u2, u1} α β s t) u) (forall (f : α -> β), (Membership.mem.{max u2 u1, max u2 u1} (α -> β) (Set.{max u2 u1} (α -> β)) (Set.instMembershipSet.{max u2 u1} (α -> β)) f s) -> (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a t) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f a) u)))
Case conversion may be inaccurate. Consider using '#align set.seq_subset Set.seq_subsetₓ'. -/
theorem seq_subset {s : Set (α → β)} {t : Set α} {u : Set β} :
    seq s t ⊆ u ↔ ∀ f ∈ s, ∀ a ∈ t, (f : α → β) a ∈ u :=
  Iff.intro (fun h f hf a ha => h ⟨f, hf, a, ha, rfl⟩) fun h b ⟨f, hf, a, ha, Eq⟩ =>
    Eq ▸ h f hf a ha
#align set.seq_subset Set.seq_subset

/- warning: set.seq_mono -> Set.seq_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₀ : Set.{max u1 u2} (α -> β)} {s₁ : Set.{max u1 u2} (α -> β)} {t₀ : Set.{u1} α} {t₁ : Set.{u1} α}, (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (α -> β)) (Set.hasSubset.{max u1 u2} (α -> β)) s₀ s₁) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t₀ t₁) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.seq.{u1, u2} α β s₀ t₀) (Set.seq.{u1, u2} α β s₁ t₁))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₀ : Set.{max u2 u1} (α -> β)} {s₁ : Set.{max u2 u1} (α -> β)} {t₀ : Set.{u2} α} {t₁ : Set.{u2} α}, (HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (α -> β)) (Set.instHasSubsetSet.{max u2 u1} (α -> β)) s₀ s₁) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) t₀ t₁) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.seq.{u2, u1} α β s₀ t₀) (Set.seq.{u2, u1} α β s₁ t₁))
Case conversion may be inaccurate. Consider using '#align set.seq_mono Set.seq_monoₓ'. -/
theorem seq_mono {s₀ s₁ : Set (α → β)} {t₀ t₁ : Set α} (hs : s₀ ⊆ s₁) (ht : t₀ ⊆ t₁) :
    seq s₀ t₀ ⊆ seq s₁ t₁ := fun b ⟨f, hf, a, ha, Eq⟩ => ⟨f, hs hf, a, ht ha, Eq⟩
#align set.seq_mono Set.seq_mono

/- warning: set.singleton_seq -> Set.singleton_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t : Set.{u1} α}, Eq.{succ u2} (Set.{u2} β) (Set.seq.{u1, u2} α β (Singleton.singleton.{max u1 u2, max u1 u2} (α -> β) (Set.{max u1 u2} (α -> β)) (Set.hasSingleton.{max u1 u2} (α -> β)) f) t) (Set.image.{u1, u2} α β f t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {t : Set.{u2} α}, Eq.{succ u1} (Set.{u1} β) (Set.seq.{u2, u1} α β (Singleton.singleton.{max u2 u1, max u2 u1} (α -> β) (Set.{max u2 u1} (α -> β)) (Set.instSingletonSet.{max u2 u1} (α -> β)) f) t) (Set.image.{u2, u1} α β f t)
Case conversion may be inaccurate. Consider using '#align set.singleton_seq Set.singleton_seqₓ'. -/
theorem singleton_seq {f : α → β} {t : Set α} : Set.seq {f} t = f '' t :=
  Set.ext <| by simp
#align set.singleton_seq Set.singleton_seq

/- warning: set.seq_singleton -> Set.seq_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{max u1 u2} (α -> β)} {a : α}, Eq.{succ u2} (Set.{u2} β) (Set.seq.{u1, u2} α β s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) (Set.image.{max u1 u2, u2} (α -> β) β (fun (f : α -> β) => f a) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{max u2 u1} (α -> β)} {a : α}, Eq.{succ u1} (Set.{u1} β) (Set.seq.{u2, u1} α β s (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) a)) (Set.image.{max u2 u1, u1} (α -> β) β (fun (f : α -> β) => f a) s)
Case conversion may be inaccurate. Consider using '#align set.seq_singleton Set.seq_singletonₓ'. -/
theorem seq_singleton {s : Set (α → β)} {a : α} : Set.seq s {a} = (fun f : α → β => f a) '' s :=
  Set.ext <| by simp
#align set.seq_singleton Set.seq_singleton

/- warning: set.seq_seq -> Set.seq_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{max u2 u3} (β -> γ)} {t : Set.{max u1 u2} (α -> β)} {u : Set.{u1} α}, Eq.{succ u3} (Set.{u3} γ) (Set.seq.{u2, u3} β γ s (Set.seq.{u1, u2} α β t u)) (Set.seq.{u1, u3} α γ (Set.seq.{max u1 u2, max u1 u3} (α -> β) (α -> γ) (Set.image.{max u2 u3, max (max u1 u2) u1 u3} (β -> γ) ((α -> β) -> α -> γ) (Function.comp.{succ u1, succ u2, succ u3} α β γ) s) t) u)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {s : Set.{max u3 u2} (β -> γ)} {t : Set.{max u1 u3} (α -> β)} {u : Set.{u1} α}, Eq.{succ u2} (Set.{u2} γ) (Set.seq.{u3, u2} β γ s (Set.seq.{u1, u3} α β t u)) (Set.seq.{u1, u2} α γ (Set.seq.{max u3 u1, max u2 u1} (α -> β) (α -> γ) (Set.image.{max u3 u2, max (max u2 u1) u3 u1} (β -> γ) ((α -> β) -> α -> γ) (fun (x._@.Mathlib.Data.Set.Lattice._hyg.31531 : β -> γ) (x._@.Mathlib.Data.Set.Lattice._hyg.31533 : α -> β) => Function.comp.{succ u1, succ u3, succ u2} α β γ x._@.Mathlib.Data.Set.Lattice._hyg.31531 x._@.Mathlib.Data.Set.Lattice._hyg.31533) s) t) u)
Case conversion may be inaccurate. Consider using '#align set.seq_seq Set.seq_seqₓ'. -/
theorem seq_seq {s : Set (β → γ)} {t : Set (α → β)} {u : Set α} :
    seq s (seq t u) = seq (seq ((· ∘ ·) '' s) t) u :=
  by
  refine' Set.ext fun c => Iff.intro _ _
  · rintro ⟨f, hfs, b, ⟨g, hg, a, hau, rfl⟩, rfl⟩
    exact ⟨f ∘ g, ⟨(· ∘ ·) f, mem_image_of_mem _ hfs, g, hg, rfl⟩, a, hau, rfl⟩
  · rintro ⟨fg, ⟨fc, ⟨f, hfs, rfl⟩, g, hgt, rfl⟩, a, ha, rfl⟩
    exact ⟨f, hfs, g a, ⟨g, hgt, a, ha, rfl⟩, rfl⟩
#align set.seq_seq Set.seq_seq

/- warning: set.image_seq -> Set.image_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : β -> γ} {s : Set.{max u1 u2} (α -> β)} {t : Set.{u1} α}, Eq.{succ u3} (Set.{u3} γ) (Set.image.{u2, u3} β γ f (Set.seq.{u1, u2} α β s t)) (Set.seq.{u1, u3} α γ (Set.image.{max u1 u2, max u1 u3} (α -> β) (α -> γ) (Function.comp.{succ u1, succ u2, succ u3} α β γ f) s) t)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : β -> γ} {s : Set.{max u3 u2} (α -> β)} {t : Set.{u3} α}, Eq.{succ u1} (Set.{u1} γ) (Set.image.{u2, u1} β γ f (Set.seq.{u3, u2} α β s t)) (Set.seq.{u3, u1} α γ (Set.image.{max u2 u3, max u1 u3} (α -> β) (α -> γ) ((fun (x._@.Mathlib.Data.Set.Lattice._hyg.31713 : β -> γ) (x._@.Mathlib.Data.Set.Lattice._hyg.31715 : α -> β) => Function.comp.{succ u3, succ u2, succ u1} α β γ x._@.Mathlib.Data.Set.Lattice._hyg.31713 x._@.Mathlib.Data.Set.Lattice._hyg.31715) f) s) t)
Case conversion may be inaccurate. Consider using '#align set.image_seq Set.image_seqₓ'. -/
theorem image_seq {f : β → γ} {s : Set (α → β)} {t : Set α} :
    f '' seq s t = seq ((· ∘ ·) f '' s) t := by
  rw [← singleton_seq, ← singleton_seq, seq_seq, image_singleton]
#align set.image_seq Set.image_seq

/- warning: set.prod_eq_seq -> Set.prod_eq_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t) (Set.seq.{u2, max u1 u2} β (Prod.{u1, u2} α β) (Set.image.{u1, max u1 u2} α (β -> (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β) s) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s t) (Set.seq.{u1, max u2 u1} β (Prod.{u2, u1} α β) (Set.image.{u2, max u1 u2} α (β -> (Prod.{u2, u1} α β)) (Prod.mk.{u2, u1} α β) s) t)
Case conversion may be inaccurate. Consider using '#align set.prod_eq_seq Set.prod_eq_seqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_eq_seq {s : Set α} {t : Set β} : s ×ˢ t = (Prod.mk '' s).seq t :=
  by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨Prod.mk a, ⟨a, ha, rfl⟩, b, hb, rfl⟩
  · rintro ⟨f, ⟨x, hx, rfl⟩, y, hy, eq⟩
    rw [← Eq]
    exact ⟨hx, hy⟩
#align set.prod_eq_seq Set.prod_eq_seq

/- warning: set.prod_image_seq_comm -> Set.prod_image_seq_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.seq.{u2, max u1 u2} β (Prod.{u1, u2} α β) (Set.image.{u1, max u1 u2} α (β -> (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β) s) t) (Set.seq.{u1, max u1 u2} α (Prod.{u1, u2} α β) (Set.image.{u2, max u1 u2} β (α -> (Prod.{u1, u2} α β)) (fun (b : β) (a : α) => Prod.mk.{u1, u2} α β a b) t) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : Set.{u1} β), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Prod.{u2, u1} α β)) (Set.seq.{u1, max u2 u1} β (Prod.{u2, u1} α β) (Set.image.{u2, max u1 u2} α (β -> (Prod.{u2, u1} α β)) (Prod.mk.{u2, u1} α β) s) t) (Set.seq.{u2, max u1 u2} α (Prod.{u2, u1} α β) (Set.image.{u1, max u1 u2} β (α -> (Prod.{u2, u1} α β)) (fun (b : β) (a : α) => Prod.mk.{u2, u1} α β a b) t) s)
Case conversion may be inaccurate. Consider using '#align set.prod_image_seq_comm Set.prod_image_seq_commₓ'. -/
theorem prod_image_seq_comm (s : Set α) (t : Set β) :
    (Prod.mk '' s).seq t = seq ((fun b a => (a, b)) '' t) s := by
  rw [← prod_eq_seq, ← image_swap_prod, prod_eq_seq, image_seq, ← image_comp, Prod.swap]
#align set.prod_image_seq_comm Set.prod_image_seq_comm

/- warning: set.image2_eq_seq -> Set.image2_eq_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (Set.seq.{u2, u3} β γ (Set.image.{u1, max u2 u3} α (β -> γ) f s) t)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (s : Set.{u3} α) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} γ) (Set.image2.{u3, u2, u1} α β γ f s t) (Set.seq.{u2, u1} β γ (Set.image.{u3, max u1 u2} α (β -> γ) f s) t)
Case conversion may be inaccurate. Consider using '#align set.image2_eq_seq Set.image2_eq_seqₓ'. -/
theorem image2_eq_seq (f : α → β → γ) (s : Set α) (t : Set β) : image2 f s t = seq (f '' s) t :=
  by
  ext
  simp
#align set.image2_eq_seq Set.image2_eq_seq

end Seq

section Pi

variable {π : α → Type _}

/- warning: set.pi_def -> Set.pi_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {π : α -> Type.{u2}} (i : Set.{u1} α) (s : forall (a : α), Set.{u2} (π a)), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : α), π i)) (Set.pi.{u1, u2} α (fun (a : α) => π a) i s) (Set.interᵢ.{max u1 u2, succ u1} (forall (i : α), π i) α (fun (a : α) => Set.interᵢ.{max u1 u2, 0} (forall (i : α), π i) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a i) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a i) => Set.preimage.{max u1 u2, u2} (forall (i : α), π i) (π a) (Function.eval.{succ u1, succ u2} α (fun (i : α) => π i) a) (s a))))
but is expected to have type
  forall {α : Type.{u2}} {π : α -> Type.{u1}} (i : Set.{u2} α) (s : forall (a : α), Set.{u1} (π a)), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : α), π i)) (Set.pi.{u2, u1} α (fun (a : α) => π a) i s) (Set.interᵢ.{max u2 u1, succ u2} (forall (i : α), π i) α (fun (a : α) => Set.interᵢ.{max u2 u1, 0} (forall (i : α), π i) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a i) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a i) => Set.preimage.{max u2 u1, u1} (forall (i : α), π i) (π a) (Function.eval.{succ u2, succ u1} α (fun (i : α) => π i) a) (s a))))
Case conversion may be inaccurate. Consider using '#align set.pi_def Set.pi_defₓ'. -/
theorem pi_def (i : Set α) (s : ∀ a, Set (π a)) : pi i s = ⋂ a ∈ i, eval a ⁻¹' s a :=
  by
  ext
  simp
#align set.pi_def Set.pi_def

#print Set.univ_pi_eq_interᵢ /-
theorem univ_pi_eq_interᵢ (t : ∀ i, Set (π i)) : pi univ t = ⋂ i, eval i ⁻¹' t i := by
  simp only [pi_def, Inter_true, mem_univ]
#align set.univ_pi_eq_Inter Set.univ_pi_eq_interᵢ
-/

/- warning: set.pi_diff_pi_subset -> Set.pi_diff_pi_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {π : α -> Type.{u2}} (i : Set.{u1} α) (s : forall (a : α), Set.{u2} (π a)) (t : forall (a : α), Set.{u2} (π a)), HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (forall (i : α), π i)) (Set.hasSubset.{max u1 u2} (forall (i : α), π i)) (SDiff.sdiff.{max u1 u2} (Set.{max u1 u2} (forall (i : α), π i)) (BooleanAlgebra.toHasSdiff.{max u1 u2} (Set.{max u1 u2} (forall (i : α), π i)) (Set.booleanAlgebra.{max u1 u2} (forall (i : α), π i))) (Set.pi.{u1, u2} α (fun (a : α) => π a) i s) (Set.pi.{u1, u2} α (fun (i : α) => π i) i t)) (Set.unionᵢ.{max u1 u2, succ u1} (forall (i : α), π i) α (fun (a : α) => Set.unionᵢ.{max u1 u2, 0} (forall (i : α), π i) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a i) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a i) => Set.preimage.{max u1 u2, u2} (forall (i : α), π i) (π a) (Function.eval.{succ u1, succ u2} α (fun (i : α) => π i) a) (SDiff.sdiff.{u2} (Set.{u2} (π a)) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} (π a)) (Set.booleanAlgebra.{u2} (π a))) (s a) (t a)))))
but is expected to have type
  forall {α : Type.{u2}} {π : α -> Type.{u1}} (i : Set.{u2} α) (s : forall (a : α), Set.{u1} (π a)) (t : forall (a : α), Set.{u1} (π a)), HasSubset.Subset.{max u1 u2} (Set.{max u2 u1} (forall (i : α), π i)) (Set.instHasSubsetSet.{max u2 u1} (forall (i : α), π i)) (SDiff.sdiff.{max u1 u2} (Set.{max u2 u1} (forall (i : α), π i)) (Set.instSDiffSet.{max u2 u1} (forall (i : α), π i)) (Set.pi.{u2, u1} α (fun (a : α) => π a) i s) (Set.pi.{u2, u1} α (fun (i : α) => π i) i t)) (Set.unionᵢ.{max u2 u1, succ u2} (forall (i : α), π i) α (fun (a : α) => Set.unionᵢ.{max u2 u1, 0} (forall (i : α), π i) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a i) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a i) => Set.preimage.{max u2 u1, u1} (forall (i : α), π i) (π a) (Function.eval.{succ u2, succ u1} α (fun (i : α) => π i) a) (SDiff.sdiff.{u1} (Set.{u1} (π a)) (Set.instSDiffSet.{u1} (π a)) (s a) (t a)))))
Case conversion may be inaccurate. Consider using '#align set.pi_diff_pi_subset Set.pi_diff_pi_subsetₓ'. -/
theorem pi_diff_pi_subset (i : Set α) (s t : ∀ a, Set (π a)) :
    pi i s \ pi i t ⊆ ⋃ a ∈ i, eval a ⁻¹' (s a \ t a) :=
  by
  refine' diff_subset_comm.2 fun x hx a ha => _
  simp only [mem_diff, mem_pi, mem_Union, not_exists, mem_preimage, not_and, not_not, eval_apply] at
    hx
  exact hx.2 _ ha (hx.1 _ ha)
#align set.pi_diff_pi_subset Set.pi_diff_pi_subset

/- warning: set.Union_univ_pi -> Set.unionᵢ_univ_pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {π : α -> Type.{u3}} (t : forall (i : α), ι -> (Set.{u3} (π i))), Eq.{succ (max u1 u3)} (Set.{max u1 u3} (forall (i : α), π i)) (Set.unionᵢ.{max u1 u3, imax (succ u1) u2} (forall (i : α), π i) (α -> ι) (fun (x : α -> ι) => Set.pi.{u1, u3} α (fun (i : α) => π i) (Set.univ.{u1} α) (fun (i : α) => t i (x i)))) (Set.pi.{u1, u3} α (fun (i : α) => π i) (Set.univ.{u1} α) (fun (i : α) => Set.unionᵢ.{u3, u2} (π i) ι (fun (j : ι) => t i j)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {π : α -> Type.{u3}} (t : forall (i : α), ι -> (Set.{u3} (π i))), Eq.{max (succ u2) (succ u3)} (Set.{max u3 u2} (forall (i : α), π i)) (Set.unionᵢ.{max u3 u2, imax (succ u2) u1} (forall (i : α), π i) (α -> ι) (fun (x : α -> ι) => Set.pi.{u2, u3} α (fun (i : α) => π i) (Set.univ.{u2} α) (fun (i : α) => t i (x i)))) (Set.pi.{u2, u3} α (fun (i : α) => π i) (Set.univ.{u2} α) (fun (i : α) => Set.unionᵢ.{u3, u1} (π i) ι (fun (j : ι) => t i j)))
Case conversion may be inaccurate. Consider using '#align set.Union_univ_pi Set.unionᵢ_univ_piₓ'. -/
theorem unionᵢ_univ_pi (t : ∀ i, ι → Set (π i)) :
    (⋃ x : α → ι, pi univ fun i => t i (x i)) = pi univ fun i => ⋃ j : ι, t i j :=
  by
  ext
  simp [Classical.skolem]
#align set.Union_univ_pi Set.unionᵢ_univ_pi

end Pi

end Set

namespace Function

namespace Surjective

/- warning: function.surjective.Union_comp -> Function.Surjective.unionᵢ_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι₂ : Sort.{u3}} {f : ι -> ι₂}, (Function.Surjective.{u2, u3} ι ι₂ f) -> (forall (g : ι₂ -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u2} α ι (fun (x : ι) => g (f x))) (Set.unionᵢ.{u1, u3} α ι₂ (fun (y : ι₂) => g y)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι₂ : Sort.{u2}} {f : ι -> ι₂}, (Function.Surjective.{u3, u2} ι ι₂ f) -> (forall (g : ι₂ -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, u3} α ι (fun (x : ι) => g (f x))) (Set.unionᵢ.{u1, u2} α ι₂ (fun (y : ι₂) => g y)))
Case conversion may be inaccurate. Consider using '#align function.surjective.Union_comp Function.Surjective.unionᵢ_compₓ'. -/
theorem unionᵢ_comp {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → Set α) : (⋃ x, g (f x)) = ⋃ y, g y :=
  hf.supr_comp g
#align function.surjective.Union_comp Function.Surjective.unionᵢ_comp

/- warning: function.surjective.Inter_comp -> Function.Surjective.interᵢ_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι₂ : Sort.{u3}} {f : ι -> ι₂}, (Function.Surjective.{u2, u3} ι ι₂ f) -> (forall (g : ι₂ -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (x : ι) => g (f x))) (Set.interᵢ.{u1, u3} α ι₂ (fun (y : ι₂) => g y)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι₂ : Sort.{u2}} {f : ι -> ι₂}, (Function.Surjective.{u3, u2} ι ι₂ f) -> (forall (g : ι₂ -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, u3} α ι (fun (x : ι) => g (f x))) (Set.interᵢ.{u1, u2} α ι₂ (fun (y : ι₂) => g y)))
Case conversion may be inaccurate. Consider using '#align function.surjective.Inter_comp Function.Surjective.interᵢ_compₓ'. -/
theorem interᵢ_comp {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → Set α) : (⋂ x, g (f x)) = ⋂ y, g y :=
  hf.infi_comp g
#align function.surjective.Inter_comp Function.Surjective.interᵢ_comp

end Surjective

end Function

/-!
### Disjoint sets

We define some lemmas in the `disjoint` namespace to be able to use projection notation.
-/


section Disjoint

variable {s t u : Set α} {f : α → β}

namespace Set

/- warning: set.disjoint_Union_left -> Set.disjoint_unionᵢ_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t : Set.{u1} α} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) t) (forall (i : ι), Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (s i) t)
but is expected to have type
  forall {α : Type.{u1}} {t : Set.{u1} α} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) t) (forall (i : ι), Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (s i) t)
Case conversion may be inaccurate. Consider using '#align set.disjoint_Union_left Set.disjoint_unionᵢ_leftₓ'. -/
@[simp]
theorem disjoint_unionᵢ_left {ι : Sort _} {s : ι → Set α} :
    Disjoint (⋃ i, s i) t ↔ ∀ i, Disjoint (s i) t :=
  supᵢ_disjoint_iff
#align set.disjoint_Union_left Set.disjoint_unionᵢ_left

/- warning: set.disjoint_Union_right -> Set.disjoint_unionᵢ_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t : Set.{u1} α} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) t (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i))) (forall (i : ι), Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) t (s i))
but is expected to have type
  forall {α : Type.{u1}} {t : Set.{u1} α} {ι : Sort.{u2}} {s : ι -> (Set.{u1} α)}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) t (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i))) (forall (i : ι), Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) t (s i))
Case conversion may be inaccurate. Consider using '#align set.disjoint_Union_right Set.disjoint_unionᵢ_rightₓ'. -/
@[simp]
theorem disjoint_unionᵢ_right {ι : Sort _} {s : ι → Set α} :
    Disjoint t (⋃ i, s i) ↔ ∀ i, Disjoint t (s i) :=
  disjoint_supᵢ_iff
#align set.disjoint_Union_right Set.disjoint_unionᵢ_right

/- warning: set.disjoint_Union₂_left -> Set.disjoint_unionᵢ₂_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : forall (i : ι), (κ i) -> (Set.{u1} α)} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) t) (forall (i : ι) (j : κ i), Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (s i j) t)
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : forall (i : ι), (κ i) -> (Set.{u3} α)} {t : Set.{u3} α}, Iff (Disjoint.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α)))))) (BoundedOrder.toOrderBot.{u3} (Set.{u3} α) (Preorder.toLE.{u3} (Set.{u3} α) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α)))))))) (CompleteLattice.toBoundedOrder.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α)))))) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) t) (forall (i : ι) (j : κ i), Disjoint.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α)))))) (BoundedOrder.toOrderBot.{u3} (Set.{u3} α) (Preorder.toLE.{u3} (Set.{u3} α) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α)))))))) (CompleteLattice.toBoundedOrder.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α)))))) (s i j) t)
Case conversion may be inaccurate. Consider using '#align set.disjoint_Union₂_left Set.disjoint_unionᵢ₂_leftₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem disjoint_unionᵢ₂_left {s : ∀ i, κ i → Set α} {t : Set α} :
    Disjoint (⋃ (i) (j), s i j) t ↔ ∀ i j, Disjoint (s i j) t :=
  supᵢ₂_disjoint_iff
#align set.disjoint_Union₂_left Set.disjoint_unionᵢ₂_left

/- warning: set.disjoint_Union₂_right -> Set.disjoint_unionᵢ₂_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} {s : Set.{u1} α} {t : forall (i : ι), (κ i) -> (Set.{u1} α)}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => t i j)))) (forall (i : ι) (j : κ i), Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (t i j))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} {s : Set.{u3} α} {t : forall (i : ι), (κ i) -> (Set.{u3} α)}, Iff (Disjoint.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α)))))) (BoundedOrder.toOrderBot.{u3} (Set.{u3} α) (Preorder.toLE.{u3} (Set.{u3} α) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α)))))))) (CompleteLattice.toBoundedOrder.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α)))))) s (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => t i j)))) (forall (i : ι) (j : κ i), Disjoint.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α)))))) (BoundedOrder.toOrderBot.{u3} (Set.{u3} α) (Preorder.toLE.{u3} (Set.{u3} α) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α)))))))) (CompleteLattice.toBoundedOrder.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α)))))) s (t i j))
Case conversion may be inaccurate. Consider using '#align set.disjoint_Union₂_right Set.disjoint_unionᵢ₂_rightₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem disjoint_unionᵢ₂_right {s : Set α} {t : ∀ i, κ i → Set α} :
    Disjoint s (⋃ (i) (j), t i j) ↔ ∀ i j, Disjoint s (t i j) :=
  disjoint_supᵢ₂_iff
#align set.disjoint_Union₂_right Set.disjoint_unionᵢ₂_right

/- warning: set.disjoint_sUnion_left -> Set.disjoint_unionₛ_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {S : Set.{u1} (Set.{u1} α)} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.unionₛ.{u1} α S) t) (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s S) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t))
but is expected to have type
  forall {α : Type.{u1}} {S : Set.{u1} (Set.{u1} α)} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.unionₛ.{u1} α S) t) (forall (s : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s S) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t))
Case conversion may be inaccurate. Consider using '#align set.disjoint_sUnion_left Set.disjoint_unionₛ_leftₓ'. -/
@[simp]
theorem disjoint_unionₛ_left {S : Set (Set α)} {t : Set α} :
    Disjoint (⋃₀ S) t ↔ ∀ s ∈ S, Disjoint s t :=
  supₛ_disjoint_iff
#align set.disjoint_sUnion_left Set.disjoint_unionₛ_left

/- warning: set.disjoint_sUnion_right -> Set.disjoint_unionₛ_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {S : Set.{u1} (Set.{u1} α)}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (Set.unionₛ.{u1} α S)) (forall (t : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t S) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {S : Set.{u1} (Set.{u1} α)}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s (Set.unionₛ.{u1} α S)) (forall (t : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) t S) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t))
Case conversion may be inaccurate. Consider using '#align set.disjoint_sUnion_right Set.disjoint_unionₛ_rightₓ'. -/
@[simp]
theorem disjoint_unionₛ_right {s : Set α} {S : Set (Set α)} :
    Disjoint s (⋃₀ S) ↔ ∀ t ∈ S, Disjoint s t :=
  disjoint_supₛ_iff
#align set.disjoint_sUnion_right Set.disjoint_unionₛ_right

end Set

end Disjoint

/-! ### Intervals -/


namespace Set

variable [CompleteLattice α]

/- warning: set.Ici_supr -> Set.Ici_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α), Eq.{succ u1} (Set.{u1} α) (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α), Eq.{succ u2} (Set.{u2} α) (Set.Ici.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => f i))) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Set.Ici.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (f i)))
Case conversion may be inaccurate. Consider using '#align set.Ici_supr Set.Ici_supᵢₓ'. -/
theorem Ici_supᵢ (f : ι → α) : Ici (⨆ i, f i) = ⋂ i, Ici (f i) :=
  ext fun _ => by simp only [mem_Ici, supᵢ_le_iff, mem_Inter]
#align set.Ici_supr Set.Ici_supᵢ

/- warning: set.Iic_infi -> Set.Iic_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α), Eq.{succ u1} (Set.{u1} α) (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => f i))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α), Eq.{succ u2} (Set.{u2} α) (Set.Iic.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => f i))) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Set.Iic.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (f i)))
Case conversion may be inaccurate. Consider using '#align set.Iic_infi Set.Iic_infᵢₓ'. -/
theorem Iic_infᵢ (f : ι → α) : Iic (⨅ i, f i) = ⋂ i, Iic (f i) :=
  ext fun _ => by simp only [mem_Iic, le_infᵢ_iff, mem_Inter]
#align set.Iic_infi Set.Iic_infᵢ

/- warning: set.Ici_supr₂ -> Set.Ici_supᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] (f : forall (i : ι), (κ i) -> α), Eq.{succ u1} (Set.{u1} α) (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j)))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (f i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] (f : forall (i : ι), (κ i) -> α), Eq.{succ u3} (Set.{u3} α) (Set.Ici.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))) (supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => supᵢ.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j)))) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => Set.Ici.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))) (f i j))))
Case conversion may be inaccurate. Consider using '#align set.Ici_supr₂ Set.Ici_supᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Ici_supᵢ₂ (f : ∀ i, κ i → α) : Ici (⨆ (i) (j), f i j) = ⋂ (i) (j), Ici (f i j) := by
  simp_rw [Ici_supr]
#align set.Ici_supr₂ Set.Ici_supᵢ₂

/- warning: set.Iic_infi₂ -> Set.Iic_infᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] (f : forall (i : ι), (κ i) -> α), Eq.{succ u1} (Set.{u1} α) (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j)))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (f i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] (f : forall (i : ι), (κ i) -> α), Eq.{succ u3} (Set.{u3} α) (Set.Iic.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))) (infᵢ.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j)))) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => Set.Iic.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))) (f i j))))
Case conversion may be inaccurate. Consider using '#align set.Iic_infi₂ Set.Iic_infᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Iic_infᵢ₂ (f : ∀ i, κ i → α) : Iic (⨅ (i) (j), f i j) = ⋂ (i) (j), Iic (f i j) := by
  simp_rw [Iic_infi]
#align set.Iic_infi₂ Set.Iic_infᵢ₂

/- warning: set.Ici_Sup -> Set.Ici_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s)) (Set.interᵢ.{u1, succ u1} α α (fun (a : α) => Set.interᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s)) (Set.interᵢ.{u1, succ u1} α α (fun (a : α) => Set.interᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) a)))
Case conversion may be inaccurate. Consider using '#align set.Ici_Sup Set.Ici_supₛₓ'. -/
theorem Ici_supₛ (s : Set α) : Ici (supₛ s) = ⋂ a ∈ s, Ici a := by rw [supₛ_eq_supᵢ, Ici_supr₂]
#align set.Ici_Sup Set.Ici_supₛ

/- warning: set.Iic_Inf -> Set.Iic_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s)) (Set.interᵢ.{u1, succ u1} α α (fun (a : α) => Set.interᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s)) (Set.interᵢ.{u1, succ u1} α α (fun (a : α) => Set.interᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) a)))
Case conversion may be inaccurate. Consider using '#align set.Iic_Inf Set.Iic_infₛₓ'. -/
theorem Iic_infₛ (s : Set α) : Iic (infₛ s) = ⋂ a ∈ s, Iic a := by rw [infₛ_eq_infᵢ, Iic_infi₂]
#align set.Iic_Inf Set.Iic_infₛ

end Set

namespace Set

variable (t : α → Set β)

/- warning: set.bUnion_diff_bUnion_subset -> Set.bunionᵢ_diff_bunionᵢ_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (t : α -> (Set.{u2} β)) (s₁ : Set.{u1} α) (s₂ : Set.{u1} α), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SDiff.sdiff.{u2} (Set.{u2} β) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s₁) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s₁) => t x))) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s₂) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s₂) => t x)))) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s₁ s₂)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s₁ s₂)) => t x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (t : α -> (Set.{u1} β)) (s₁ : Set.{u2} α) (s₂ : Set.{u2} α), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (SDiff.sdiff.{u1} (Set.{u1} β) (Set.instSDiffSet.{u1} β) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s₁) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s₁) => t x))) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s₂) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s₂) => t x)))) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s₁ s₂)) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s₁ s₂)) => t x)))
Case conversion may be inaccurate. Consider using '#align set.bUnion_diff_bUnion_subset Set.bunionᵢ_diff_bunionᵢ_subsetₓ'. -/
theorem bunionᵢ_diff_bunionᵢ_subset (s₁ s₂ : Set α) :
    ((⋃ x ∈ s₁, t x) \ ⋃ x ∈ s₂, t x) ⊆ ⋃ x ∈ s₁ \ s₂, t x :=
  by
  simp only [diff_subset_iff, ← bUnion_union]
  apply bUnion_subset_bUnion_left
  rw [union_diff_self]
  apply subset_union_right
#align set.bUnion_diff_bUnion_subset Set.bunionᵢ_diff_bunionᵢ_subset

#print Set.sigmaToUnionᵢ /-
/-- If `t` is an indexed family of sets, then there is a natural map from `Σ i, t i` to `⋃ i, t i`
sending `⟨i, x⟩` to `x`. -/
def sigmaToUnionᵢ (x : Σi, t i) : ⋃ i, t i :=
  ⟨x.2, mem_unionᵢ.2 ⟨x.1, x.2.2⟩⟩
#align set.sigma_to_Union Set.sigmaToUnionᵢ
-/

/- warning: set.sigma_to_Union_surjective -> Set.sigmaToUnionᵢ_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (t : α -> (Set.{u2} β)), Function.Surjective.{max (succ u1) (succ u2), succ u2} (Sigma.{u1, u2} α (fun (i : α) => coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i))) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (i : α) => t i))) (Set.sigmaToUnionᵢ.{u1, u2} α β t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (t : α -> (Set.{u1} β)), Function.Surjective.{max (succ u2) (succ u1), succ u1} (Sigma.{u2, u1} α (fun (i : α) => Set.Elem.{u1} β (t i))) (Set.Elem.{u1} β (Set.unionᵢ.{u1, succ u2} β α (fun (i : α) => t i))) (Set.sigmaToUnionᵢ.{u2, u1} α β t)
Case conversion may be inaccurate. Consider using '#align set.sigma_to_Union_surjective Set.sigmaToUnionᵢ_surjectiveₓ'. -/
theorem sigmaToUnionᵢ_surjective : Surjective (sigmaToUnionᵢ t)
  | ⟨b, hb⟩ =>
    have : ∃ a, b ∈ t a := by simpa using hb
    let ⟨a, hb⟩ := this
    ⟨⟨a, b, hb⟩, rfl⟩
#align set.sigma_to_Union_surjective Set.sigmaToUnionᵢ_surjective

/- warning: set.sigma_to_Union_injective -> Set.sigmaToUnionᵢ_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (t : α -> (Set.{u2} β)), (forall (i : α) (j : α), (Ne.{succ u1} α i j) -> (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) (t i) (t j))) -> (Function.Injective.{max (succ u1) (succ u2), succ u2} (Sigma.{u1, u2} α (fun (i : α) => coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i))) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (i : α) => t i))) (Set.sigmaToUnionᵢ.{u1, u2} α β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (t : α -> (Set.{u1} β)), (forall (i : α) (j : α), (Ne.{succ u2} α i j) -> (Disjoint.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} β) (Preorder.toLE.{u1} (Set.{u1} β) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))) (t i) (t j))) -> (Function.Injective.{max (succ u2) (succ u1), succ u1} (Sigma.{u2, u1} α (fun (i : α) => Set.Elem.{u1} β (t i))) (Set.Elem.{u1} β (Set.unionᵢ.{u1, succ u2} β α (fun (i : α) => t i))) (Set.sigmaToUnionᵢ.{u2, u1} α β t))
Case conversion may be inaccurate. Consider using '#align set.sigma_to_Union_injective Set.sigmaToUnionᵢ_injectiveₓ'. -/
theorem sigmaToUnionᵢ_injective (h : ∀ i j, i ≠ j → Disjoint (t i) (t j)) :
    Injective (sigmaToUnionᵢ t)
  | ⟨a₁, b₁, h₁⟩, ⟨a₂, b₂, h₂⟩, Eq =>
    have b_eq : b₁ = b₂ := congr_arg Subtype.val Eq
    have a_eq : a₁ = a₂ :=
      by_contradiction fun ne =>
        have : b₁ ∈ t a₁ ∩ t a₂ := ⟨h₁, b_eq.symm ▸ h₂⟩
        (h _ _ Ne).le_bot this
    Sigma.eq a_eq <| Subtype.eq <| by subst b_eq <;> subst a_eq
#align set.sigma_to_Union_injective Set.sigmaToUnionᵢ_injective

/- warning: set.sigma_to_Union_bijective -> Set.sigmaToUnionᵢ_bijective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (t : α -> (Set.{u2} β)), (forall (i : α) (j : α), (Ne.{succ u1} α i j) -> (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) (t i) (t j))) -> (Function.Bijective.{max (succ u1) (succ u2), succ u2} (Sigma.{u1, u2} α (fun (i : α) => coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i))) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (i : α) => t i))) (Set.sigmaToUnionᵢ.{u1, u2} α β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (t : α -> (Set.{u1} β)), (forall (i : α) (j : α), (Ne.{succ u2} α i j) -> (Disjoint.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} β) (Preorder.toLE.{u1} (Set.{u1} β) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))) (t i) (t j))) -> (Function.Bijective.{max (succ u2) (succ u1), succ u1} (Sigma.{u2, u1} α (fun (i : α) => Set.Elem.{u1} β (t i))) (Set.Elem.{u1} β (Set.unionᵢ.{u1, succ u2} β α (fun (i : α) => t i))) (Set.sigmaToUnionᵢ.{u2, u1} α β t))
Case conversion may be inaccurate. Consider using '#align set.sigma_to_Union_bijective Set.sigmaToUnionᵢ_bijectiveₓ'. -/
theorem sigmaToUnionᵢ_bijective (h : ∀ i j, i ≠ j → Disjoint (t i) (t j)) :
    Bijective (sigmaToUnionᵢ t) :=
  ⟨sigmaToUnionᵢ_injective t h, sigmaToUnionᵢ_surjective t⟩
#align set.sigma_to_Union_bijective Set.sigmaToUnionᵢ_bijective

/- warning: set.Union_eq_sigma_of_disjoint -> Set.unionEqSigmaOfDisjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t : α -> (Set.{u2} β)}, (forall (i : α) (j : α), (Ne.{succ u1} α i j) -> (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) (t i) (t j))) -> (Equiv.{succ u2, max (succ u1) (succ u2)} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (i : α) => t i))) (Sigma.{u1, u2} α (fun (i : α) => coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (t i))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {t : α -> (Set.{u2} β)}, (forall (i : α) (j : α), (Ne.{succ u1} α i j) -> (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} β) (Preorder.toLE.{u2} (Set.{u2} β) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))))) (t i) (t j))) -> (Equiv.{succ u2, max (succ u2) (succ u1)} (Set.Elem.{u2} β (Set.unionᵢ.{u2, succ u1} β α (fun (i : α) => t i))) (Sigma.{u1, u2} α (fun (i : α) => Set.Elem.{u2} β (t i))))
Case conversion may be inaccurate. Consider using '#align set.Union_eq_sigma_of_disjoint Set.unionEqSigmaOfDisjointₓ'. -/
/-- Equivalence between a disjoint union and a dependent sum. -/
noncomputable def unionEqSigmaOfDisjoint {t : α → Set β} (h : ∀ i j, i ≠ j → Disjoint (t i) (t j)) :
    (⋃ i, t i) ≃ Σi, t i :=
  (Equiv.ofBijective _ <| sigmaToUnionᵢ_bijective t h).symm
#align set.Union_eq_sigma_of_disjoint Set.unionEqSigmaOfDisjoint

#print Set.unionᵢ_ge_eq_unionᵢ_nat_add /-
theorem unionᵢ_ge_eq_unionᵢ_nat_add (u : ℕ → Set α) (n : ℕ) : (⋃ i ≥ n, u i) = ⋃ i, u (i + n) :=
  supᵢ_ge_eq_supᵢ_nat_add u n
#align set.Union_ge_eq_Union_nat_add Set.unionᵢ_ge_eq_unionᵢ_nat_add
-/

#print Set.interᵢ_ge_eq_interᵢ_nat_add /-
theorem interᵢ_ge_eq_interᵢ_nat_add (u : ℕ → Set α) (n : ℕ) : (⋂ i ≥ n, u i) = ⋂ i, u (i + n) :=
  infᵢ_ge_eq_infᵢ_nat_add u n
#align set.Inter_ge_eq_Inter_nat_add Set.interᵢ_ge_eq_interᵢ_nat_add
-/

/- warning: monotone.Union_nat_add -> Monotone.unionᵢ_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Nat -> (Set.{u1} α)}, (Monotone.{0, u1} Nat (Set.{u1} α) (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (LinearOrder.toLattice.{0} Nat Nat.linearOrder)))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) f) -> (forall (k : Nat), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, 1} α Nat (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n k))) (Set.unionᵢ.{u1, 1} α Nat (fun (n : Nat) => f n)))
but is expected to have type
  forall {α : Type.{u1}} {f : Nat -> (Set.{u1} α)}, (Monotone.{0, u1} Nat (Set.{u1} α) (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (DistribLattice.toLattice.{0} Nat instDistribLatticeNat)))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) f) -> (forall (k : Nat), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, 1} α Nat (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n k))) (Set.unionᵢ.{u1, 1} α Nat (fun (n : Nat) => f n)))
Case conversion may be inaccurate. Consider using '#align monotone.Union_nat_add Monotone.unionᵢ_nat_addₓ'. -/
theorem Monotone.unionᵢ_nat_add {f : ℕ → Set α} (hf : Monotone f) (k : ℕ) :
    (⋃ n, f (n + k)) = ⋃ n, f n :=
  hf.supr_nat_add k
#align monotone.Union_nat_add Monotone.unionᵢ_nat_add

/- warning: antitone.Inter_nat_add -> Antitone.interᵢ_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Nat -> (Set.{u1} α)}, (Antitone.{0, u1} Nat (Set.{u1} α) (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (LinearOrder.toLattice.{0} Nat Nat.linearOrder)))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) f) -> (forall (k : Nat), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, 1} α Nat (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n k))) (Set.interᵢ.{u1, 1} α Nat (fun (n : Nat) => f n)))
but is expected to have type
  forall {α : Type.{u1}} {f : Nat -> (Set.{u1} α)}, (Antitone.{0, u1} Nat (Set.{u1} α) (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (DistribLattice.toLattice.{0} Nat instDistribLatticeNat)))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) f) -> (forall (k : Nat), Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, 1} α Nat (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n k))) (Set.interᵢ.{u1, 1} α Nat (fun (n : Nat) => f n)))
Case conversion may be inaccurate. Consider using '#align antitone.Inter_nat_add Antitone.interᵢ_nat_addₓ'. -/
theorem Antitone.interᵢ_nat_add {f : ℕ → Set α} (hf : Antitone f) (k : ℕ) :
    (⋂ n, f (n + k)) = ⋂ n, f n :=
  hf.infi_nat_add k
#align antitone.Inter_nat_add Antitone.interᵢ_nat_add

#print Set.unionᵢ_interᵢ_ge_nat_add /-
@[simp]
theorem unionᵢ_interᵢ_ge_nat_add (f : ℕ → Set α) (k : ℕ) :
    (⋃ n, ⋂ i ≥ n, f (i + k)) = ⋃ n, ⋂ i ≥ n, f i :=
  supᵢ_infᵢ_ge_nat_add f k
#align set.Union_Inter_ge_nat_add Set.unionᵢ_interᵢ_ge_nat_add
-/

/- warning: set.union_Union_nat_succ -> Set.union_unionᵢ_nat_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (u : Nat -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (u (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Set.unionᵢ.{u1, 1} α Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Set.unionᵢ.{u1, 1} α Nat (fun (i : Nat) => u i))
but is expected to have type
  forall {α : Type.{u1}} (u : Nat -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (u (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Set.unionᵢ.{u1, 1} α Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (Set.unionᵢ.{u1, 1} α Nat (fun (i : Nat) => u i))
Case conversion may be inaccurate. Consider using '#align set.union_Union_nat_succ Set.union_unionᵢ_nat_succₓ'. -/
theorem union_unionᵢ_nat_succ (u : ℕ → Set α) : (u 0 ∪ ⋃ i, u (i + 1)) = ⋃ i, u i :=
  sup_supᵢ_nat_succ u
#align set.union_Union_nat_succ Set.union_unionᵢ_nat_succ

/- warning: set.inter_Inter_nat_succ -> Set.inter_interᵢ_nat_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (u : Nat -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (u (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Set.interᵢ.{u1, 1} α Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Set.interᵢ.{u1, 1} α Nat (fun (i : Nat) => u i))
but is expected to have type
  forall {α : Type.{u1}} (u : Nat -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (u (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Set.interᵢ.{u1, 1} α Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (Set.interᵢ.{u1, 1} α Nat (fun (i : Nat) => u i))
Case conversion may be inaccurate. Consider using '#align set.inter_Inter_nat_succ Set.inter_interᵢ_nat_succₓ'. -/
theorem inter_interᵢ_nat_succ (u : ℕ → Set α) : (u 0 ∩ ⋂ i, u (i + 1)) = ⋂ i, u i :=
  inf_infᵢ_nat_succ u
#align set.inter_Inter_nat_succ Set.inter_interᵢ_nat_succ

end Set

open Set

variable [CompleteLattice β]

/- warning: supr_Union -> supᵢ_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u2} β] (s : ι -> (Set.{u1} α)) (f : α -> β), Eq.{succ u2} β (supᵢ.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i))) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i))) => f a))) (supᵢ.{u2, u3} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) ι (fun (i : ι) => supᵢ.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (s i)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (s i)) => f a))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} β] (s : ι -> (Set.{u3} α)) (f : α -> β), Eq.{succ u2} β (supᵢ.{u2, succ u3} β (CompleteLattice.toSupSet.{u2} β _inst_1) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_1) (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i))) (fun (H : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i))) => f a))) (supᵢ.{u2, u1} β (CompleteLattice.toSupSet.{u2} β _inst_1) ι (fun (i : ι) => supᵢ.{u2, succ u3} β (CompleteLattice.toSupSet.{u2} β _inst_1) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_1) (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (s i)) (fun (H : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (s i)) => f a))))
Case conversion may be inaccurate. Consider using '#align supr_Union supᵢ_unionᵢₓ'. -/
theorem supᵢ_unionᵢ (s : ι → Set α) (f : α → β) : (⨆ a ∈ ⋃ i, s i, f a) = ⨆ (i) (a ∈ s i), f a :=
  by
  rw [supᵢ_comm]
  simp_rw [mem_Union, supᵢ_exists]
#align supr_Union supᵢ_unionᵢ

/- warning: infi_Union -> infᵢ_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u2} β] (s : ι -> (Set.{u1} α)) (f : α -> β), Eq.{succ u2} β (infᵢ.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i))) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i))) => f a))) (infᵢ.{u2, u3} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) ι (fun (i : ι) => infᵢ.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (s i)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (s i)) => f a))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} β] (s : ι -> (Set.{u3} α)) (f : α -> β), Eq.{succ u2} β (infᵢ.{u2, succ u3} β (CompleteLattice.toInfSet.{u2} β _inst_1) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_1) (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i))) (fun (H : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i))) => f a))) (infᵢ.{u2, u1} β (CompleteLattice.toInfSet.{u2} β _inst_1) ι (fun (i : ι) => infᵢ.{u2, succ u3} β (CompleteLattice.toInfSet.{u2} β _inst_1) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_1) (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (s i)) (fun (H : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (s i)) => f a))))
Case conversion may be inaccurate. Consider using '#align infi_Union infᵢ_unionᵢₓ'. -/
theorem infᵢ_unionᵢ (s : ι → Set α) (f : α → β) : (⨅ a ∈ ⋃ i, s i, f a) = ⨅ (i) (a ∈ s i), f a :=
  @supᵢ_unionᵢ α βᵒᵈ _ _ s f
#align infi_Union infᵢ_unionᵢ

/- warning: Sup_sUnion -> supₛ_unionₛ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CompleteLattice.{u1} β] (s : Set.{u1} (Set.{u1} β)), Eq.{succ u1} β (SupSet.supₛ.{u1} β (CompleteSemilatticeSup.toHasSup.{u1} β (CompleteLattice.toCompleteSemilatticeSup.{u1} β _inst_1)) (Set.unionₛ.{u1} β s)) (supᵢ.{u1, succ u1} β (CompleteSemilatticeSup.toHasSup.{u1} β (CompleteLattice.toCompleteSemilatticeSup.{u1} β _inst_1)) (Set.{u1} β) (fun (t : Set.{u1} β) => supᵢ.{u1, 0} β (CompleteSemilatticeSup.toHasSup.{u1} β (CompleteLattice.toCompleteSemilatticeSup.{u1} β _inst_1)) (Membership.Mem.{u1, u1} (Set.{u1} β) (Set.{u1} (Set.{u1} β)) (Set.hasMem.{u1} (Set.{u1} β)) t s) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} β) (Set.{u1} (Set.{u1} β)) (Set.hasMem.{u1} (Set.{u1} β)) t s) => SupSet.supₛ.{u1} β (CompleteSemilatticeSup.toHasSup.{u1} β (CompleteLattice.toCompleteSemilatticeSup.{u1} β _inst_1)) t)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CompleteLattice.{u1} β] (s : Set.{u1} (Set.{u1} β)), Eq.{succ u1} β (SupSet.supₛ.{u1} β (CompleteLattice.toSupSet.{u1} β _inst_1) (Set.unionₛ.{u1} β s)) (supᵢ.{u1, succ u1} β (CompleteLattice.toSupSet.{u1} β _inst_1) (Set.{u1} β) (fun (t : Set.{u1} β) => supᵢ.{u1, 0} β (CompleteLattice.toSupSet.{u1} β _inst_1) (Membership.mem.{u1, u1} (Set.{u1} β) (Set.{u1} (Set.{u1} β)) (Set.instMembershipSet.{u1} (Set.{u1} β)) t s) (fun (H : Membership.mem.{u1, u1} (Set.{u1} β) (Set.{u1} (Set.{u1} β)) (Set.instMembershipSet.{u1} (Set.{u1} β)) t s) => SupSet.supₛ.{u1} β (CompleteLattice.toSupSet.{u1} β _inst_1) t)))
Case conversion may be inaccurate. Consider using '#align Sup_sUnion supₛ_unionₛₓ'. -/
theorem supₛ_unionₛ (s : Set (Set β)) : supₛ (⋃₀ s) = ⨆ t ∈ s, supₛ t := by
  simp only [sUnion_eq_bUnion, supₛ_eq_supᵢ, supᵢ_unionᵢ]
#align Sup_sUnion supₛ_unionₛ

/- warning: Inf_sUnion -> infₛ_unionₛ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CompleteLattice.{u1} β] (s : Set.{u1} (Set.{u1} β)), Eq.{succ u1} β (InfSet.infₛ.{u1} β (CompleteSemilatticeInf.toHasInf.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_1)) (Set.unionₛ.{u1} β s)) (infᵢ.{u1, succ u1} β (CompleteSemilatticeInf.toHasInf.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_1)) (Set.{u1} β) (fun (t : Set.{u1} β) => infᵢ.{u1, 0} β (CompleteSemilatticeInf.toHasInf.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_1)) (Membership.Mem.{u1, u1} (Set.{u1} β) (Set.{u1} (Set.{u1} β)) (Set.hasMem.{u1} (Set.{u1} β)) t s) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} β) (Set.{u1} (Set.{u1} β)) (Set.hasMem.{u1} (Set.{u1} β)) t s) => InfSet.infₛ.{u1} β (CompleteSemilatticeInf.toHasInf.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_1)) t)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CompleteLattice.{u1} β] (s : Set.{u1} (Set.{u1} β)), Eq.{succ u1} β (InfSet.infₛ.{u1} β (CompleteLattice.toInfSet.{u1} β _inst_1) (Set.unionₛ.{u1} β s)) (infᵢ.{u1, succ u1} β (CompleteLattice.toInfSet.{u1} β _inst_1) (Set.{u1} β) (fun (t : Set.{u1} β) => infᵢ.{u1, 0} β (CompleteLattice.toInfSet.{u1} β _inst_1) (Membership.mem.{u1, u1} (Set.{u1} β) (Set.{u1} (Set.{u1} β)) (Set.instMembershipSet.{u1} (Set.{u1} β)) t s) (fun (H : Membership.mem.{u1, u1} (Set.{u1} β) (Set.{u1} (Set.{u1} β)) (Set.instMembershipSet.{u1} (Set.{u1} β)) t s) => InfSet.infₛ.{u1} β (CompleteLattice.toInfSet.{u1} β _inst_1) t)))
Case conversion may be inaccurate. Consider using '#align Inf_sUnion infₛ_unionₛₓ'. -/
theorem infₛ_unionₛ (s : Set (Set β)) : infₛ (⋃₀ s) = ⨅ t ∈ s, infₛ t :=
  @supₛ_unionₛ βᵒᵈ _ _
#align Inf_sUnion infₛ_unionₛ

