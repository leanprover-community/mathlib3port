/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.set.sigma
! leanprover-community/mathlib commit 706d88f2b8fdfeb0b22796433d7a6c1a010af9f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Image

/-!
# Sets in sigma types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/982
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `set.sigma`, the indexed sum of sets.
-/


namespace Set

variable {ι ι' : Type _} {α β : ι → Type _} {s s₁ s₂ : Set ι} {t t₁ t₂ : ∀ i, Set (α i)}
  {u : Set (Σi, α i)} {x : Σi, α i} {i j : ι} {a : α i}

@[simp]
theorem range_sigma_mk (i : ι) : range (Sigma.mk i : α i → Sigma α) = Sigma.fst ⁻¹' {i} := by
  apply subset.antisymm
  · rintro _ ⟨b, rfl⟩
    simp
  · rintro ⟨x, y⟩ (rfl | _)
    exact mem_range_self y
#align set.range_sigma_mk Set.range_sigma_mk

theorem preimage_image_sigma_mk_of_ne (h : i ≠ j) (s : Set (α j)) :
    Sigma.mk i ⁻¹' (Sigma.mk j '' s) = ∅ := by 
  ext x
  simp [h.symm]
#align set.preimage_image_sigma_mk_of_ne Set.preimage_image_sigma_mk_of_ne

theorem image_sigma_mk_preimage_sigma_map_subset {β : ι' → Type _} (f : ι → ι')
    (g : ∀ i, α i → β (f i)) (i : ι) (s : Set (β (f i))) :
    Sigma.mk i '' (g i ⁻¹' s) ⊆ Sigma.map f g ⁻¹' (Sigma.mk (f i) '' s) :=
  image_subset_iff.2 fun x hx => ⟨g i x, hx, rfl⟩
#align set.image_sigma_mk_preimage_sigma_map_subset Set.image_sigma_mk_preimage_sigma_map_subset

theorem image_sigma_mk_preimage_sigma_map {β : ι' → Type _} {f : ι → ι'} (hf : Function.Injective f)
    (g : ∀ i, α i → β (f i)) (i : ι) (s : Set (β (f i))) :
    Sigma.mk i '' (g i ⁻¹' s) = Sigma.map f g ⁻¹' (Sigma.mk (f i) '' s) := by
  refine' (image_sigma_mk_preimage_sigma_map_subset f g i s).antisymm _
  rintro ⟨j, x⟩ ⟨y, hys, hxy⟩
  simp only [hf.eq_iff, Sigma.map] at hxy
  rcases hxy with ⟨rfl, hxy⟩; rw [heq_iff_eq] at hxy; subst y
  exact ⟨x, hys, rfl⟩
#align set.image_sigma_mk_preimage_sigma_map Set.image_sigma_mk_preimage_sigma_map

#print Set.Sigma /-
/-- Indexed sum of sets. `s.sigma t` is the set of dependent pairs `⟨i, a⟩` such that `i ∈ s` and
`a ∈ t i`.-/
protected def Sigma (s : Set ι) (t : ∀ i, Set (α i)) : Set (Σi, α i) :=
  { x | x.1 ∈ s ∧ x.2 ∈ t x.1 }
#align set.sigma Set.Sigma
-/

/- warning: set.mem_sigma_iff -> Set.mem_sigma_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {x : Sigma.{u1, u2} ι (fun (i : ι) => α i)}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasMem.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) x (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) (And (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) x) s) (Membership.Mem.{u2, u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) x)) (Set.{u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) x))) (Set.hasMem.{u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) x))) (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) x) (t (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) x))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {x : Sigma.{u2, u1} ι (fun (i : ι) => α i)}, Iff (Membership.mem.{max u2 u1, max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instMembershipSet.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) x (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) (And (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) x) s) (Membership.mem.{u1, u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) x)) (Set.{u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) x))) (Set.instMembershipSet.{u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) x))) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) x) (t (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) x))))
Case conversion may be inaccurate. Consider using '#align set.mem_sigma_iff Set.mem_sigma_iffₓ'. -/
@[simp]
theorem mem_sigma_iff : x ∈ s.Sigma t ↔ x.1 ∈ s ∧ x.2 ∈ t x.1 :=
  Iff.rfl
#align set.mem_sigma_iff Set.mem_sigma_iff

/- warning: set.mk_sigma_iff -> Set.mk_sigma_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {i : ι} {a : α i}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasMem.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i a) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) (And (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (Membership.Mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasMem.{u2} (α i)) a (t i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {i : ι} {a : α i}, Iff (Membership.mem.{max u2 u1, max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instMembershipSet.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Sigma.mk.{u2, u1} ι (fun (i : ι) => α i) i a) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) (And (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (Membership.mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.instMembershipSet.{u1} (α i)) a (t i)))
Case conversion may be inaccurate. Consider using '#align set.mk_sigma_iff Set.mk_sigma_iffₓ'. -/
@[simp]
theorem mk_sigma_iff : (⟨i, a⟩ : Σi, α i) ∈ s.Sigma t ↔ i ∈ s ∧ a ∈ t i :=
  Iff.rfl
#align set.mk_sigma_iff Set.mk_sigma_iff

/- warning: set.mk_mem_sigma -> Set.mk_mem_sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {i : ι} {a : α i}, (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (Membership.Mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasMem.{u2} (α i)) a (t i)) -> (Membership.Mem.{max u1 u2, max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasMem.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i a) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {i : ι} {a : α i}, (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (Membership.mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.instMembershipSet.{u1} (α i)) a (t i)) -> (Membership.mem.{max u2 u1, max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instMembershipSet.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Sigma.mk.{u2, u1} ι (fun (i : ι) => α i) i a) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t))
Case conversion may be inaccurate. Consider using '#align set.mk_mem_sigma Set.mk_mem_sigmaₓ'. -/
theorem mk_mem_sigma (hi : i ∈ s) (ha : a ∈ t i) : (⟨i, a⟩ : Σi, α i) ∈ s.Sigma t :=
  ⟨hi, ha⟩
#align set.mk_mem_sigma Set.mk_mem_sigma

/- warning: set.sigma_mono -> Set.sigma_mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s₁ : Set.{u1} ι} {s₂ : Set.{u1} ι} {t₁ : forall (i : ι), Set.{u2} (α i)} {t₂ : forall (i : ι), Set.{u2} (α i)}, (HasSubset.Subset.{u1} (Set.{u1} ι) (Set.hasSubset.{u1} ι) s₁ s₂) -> (forall (i : ι), HasSubset.Subset.{u2} (Set.{u2} (α i)) (Set.hasSubset.{u2} (α i)) (t₁ i) (t₂ i)) -> (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasSubset.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s₁ t₁) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s₂ t₂))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s₁ : Set.{u2} ι} {s₂ : Set.{u2} ι} {t₁ : forall (i : ι), Set.{u1} (α i)} {t₂ : forall (i : ι), Set.{u1} (α i)}, (HasSubset.Subset.{u2} (Set.{u2} ι) (Set.instHasSubsetSet_1.{u2} ι) s₁ s₂) -> (forall (i : ι), HasSubset.Subset.{u1} (Set.{u1} (α i)) (Set.instHasSubsetSet_1.{u1} (α i)) (t₁ i) (t₂ i)) -> (HasSubset.Subset.{max u2 u1} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instHasSubsetSet_1.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s₁ t₁) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s₂ t₂))
Case conversion may be inaccurate. Consider using '#align set.sigma_mono Set.sigma_monoₓ'. -/
theorem sigma_mono (hs : s₁ ⊆ s₂) (ht : ∀ i, t₁ i ⊆ t₂ i) : s₁.Sigma t₁ ⊆ s₂.Sigma t₂ := fun x hx =>
  ⟨hs hx.1, ht _ hx.2⟩
#align set.sigma_mono Set.sigma_mono

/- warning: set.sigma_subset_iff -> Set.sigma_subset_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {u : Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))}, Iff (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasSubset.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t) u) (forall {{i : ι}}, (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (forall {{a : α i}}, (Membership.Mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasMem.{u2} (α i)) a (t i)) -> (Membership.Mem.{max u1 u2, max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasMem.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i a) u)))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {u : Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))}, Iff (HasSubset.Subset.{max u2 u1} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instHasSubsetSet_1.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t) u) (forall {{i : ι}}, (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (forall {{a : α i}}, (Membership.mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.instMembershipSet.{u1} (α i)) a (t i)) -> (Membership.mem.{max u2 u1, max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instMembershipSet.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Sigma.mk.{u2, u1} ι (fun (i : ι) => α i) i a) u)))
Case conversion may be inaccurate. Consider using '#align set.sigma_subset_iff Set.sigma_subset_iffₓ'. -/
theorem sigma_subset_iff : s.Sigma t ⊆ u ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃a⦄, a ∈ t i → (⟨i, a⟩ : Σi, α i) ∈ u :=
  ⟨fun h i hi a ha => h <| mk_mem_sigma hi ha, fun h ⟨i, a⟩ ha => h ha.1 ha.2⟩
#align set.sigma_subset_iff Set.sigma_subset_iff

/- warning: set.forall_sigma_iff -> Set.forall_sigma_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {p : (Sigma.{u1, u2} ι (fun (i : ι) => α i)) -> Prop}, Iff (forall (x : Sigma.{u1, u2} ι (fun (i : ι) => α i)), (Membership.Mem.{max u1 u2, max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasMem.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) x (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) -> (p x)) (forall {{i : ι}}, (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (forall {{a : α i}}, (Membership.Mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasMem.{u2} (α i)) a (t i)) -> (p (Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i a))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {p : (Sigma.{u2, u1} ι (fun (i : ι) => α i)) -> Prop}, Iff (forall (x : Sigma.{u2, u1} ι (fun (i : ι) => α i)), (Membership.mem.{max u2 u1, max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instMembershipSet.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) x (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) -> (p x)) (forall {{i : ι}}, (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (forall {{a : α i}}, (Membership.mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.instMembershipSet.{u1} (α i)) a (t i)) -> (p (Sigma.mk.{u2, u1} ι (fun (i : ι) => α i) i a))))
Case conversion may be inaccurate. Consider using '#align set.forall_sigma_iff Set.forall_sigma_iffₓ'. -/
theorem forall_sigma_iff {p : (Σi, α i) → Prop} :
    (∀ x ∈ s.Sigma t, p x) ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃a⦄, a ∈ t i → p ⟨i, a⟩ :=
  sigma_subset_iff
#align set.forall_sigma_iff Set.forall_sigma_iff

/- warning: set.exists_sigma_iff -> Set.exists_sigma_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {p : (Sigma.{u1, u2} ι (fun (i : ι) => α i)) -> Prop}, Iff (Exists.{succ (max u1 u2)} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (fun (x : Sigma.{u1, u2} ι (fun (i : ι) => α i)) => Exists.{0} (Membership.Mem.{max u1 u2, max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasMem.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) x (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasMem.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) x (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) => p x))) (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => Exists.{succ u2} (α i) (fun (a : α i) => Exists.{0} (Membership.Mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasMem.{u2} (α i)) a (t i)) (fun (H : Membership.Mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasMem.{u2} (α i)) a (t i)) => p (Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i a))))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {p : (Sigma.{u2, u1} ι (fun (i : ι) => α i)) -> Prop}, Iff (Exists.{succ (max u2 u1)} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (fun (x : Sigma.{u2, u1} ι (fun (i : ι) => α i)) => And (Membership.mem.{max u2 u1, max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instMembershipSet.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) x (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) (p x))) (Exists.{succ u2} ι (fun (i : ι) => And (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (Exists.{succ u1} (α i) (fun (a : α i) => And (Membership.mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.instMembershipSet.{u1} (α i)) a (t i)) (p (Sigma.mk.{u2, u1} ι (fun (i : ι) => α i) i a))))))
Case conversion may be inaccurate. Consider using '#align set.exists_sigma_iff Set.exists_sigma_iffₓ'. -/
theorem exists_sigma_iff {p : (Σi, α i) → Prop} :
    (∃ x ∈ s.Sigma t, p x) ↔ ∃ i ∈ s, ∃ a ∈ t i, p ⟨i, a⟩ :=
  ⟨fun ⟨⟨i, a⟩, ha, h⟩ => ⟨i, ha.1, a, ha.2, h⟩, fun ⟨i, hi, a, ha, h⟩ => ⟨⟨i, a⟩, ⟨hi, ha⟩, h⟩⟩
#align set.exists_sigma_iff Set.exists_sigma_iff

/- warning: set.sigma_empty -> Set.sigma_empty is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s (fun (i : ι) => EmptyCollection.emptyCollection.{u2} (Set.{u2} (α i)) (Set.hasEmptyc.{u2} (α i)))) (EmptyCollection.emptyCollection.{max u1 u2} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasEmptyc.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s (fun (i : ι) => EmptyCollection.emptyCollection.{u1} (Set.{u1} (α i)) (Set.instEmptyCollectionSet.{u1} (α i)))) (EmptyCollection.emptyCollection.{max u2 u1} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instEmptyCollectionSet.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))))
Case conversion may be inaccurate. Consider using '#align set.sigma_empty Set.sigma_emptyₓ'. -/
@[simp]
theorem sigma_empty : (s.Sigma fun i => (∅ : Set (α i))) = ∅ :=
  ext fun _ => and_false_iff _
#align set.sigma_empty Set.sigma_empty

/- warning: set.empty_sigma -> Set.empty_sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {t : forall (i : ι), Set.{u2} (α i)}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) (EmptyCollection.emptyCollection.{u1} (Set.{u1} ι) (Set.hasEmptyc.{u1} ι)) t) (EmptyCollection.emptyCollection.{max u1 u2} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasEmptyc.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {t : forall (i : ι), Set.{u1} (α i)}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) (EmptyCollection.emptyCollection.{u2} (Set.{u2} ι) (Set.instEmptyCollectionSet.{u2} ι)) t) (EmptyCollection.emptyCollection.{max u2 u1} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instEmptyCollectionSet.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))))
Case conversion may be inaccurate. Consider using '#align set.empty_sigma Set.empty_sigmaₓ'. -/
@[simp]
theorem empty_sigma : (∅ : Set ι).Sigma t = ∅ :=
  ext fun _ => false_and_iff _
#align set.empty_sigma Set.empty_sigma

/- warning: set.univ_sigma_univ -> Set.univ_sigma_univ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {i : ι}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i_1 : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (_x : ι) => α i) (Set.univ.{u1} ι) (fun (_x : ι) => Set.univ.{u2} (α i))) (Set.univ.{max u1 u2} (Sigma.{u1, u2} ι (fun (i_1 : ι) => α i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {i : ι}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i_1 : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (_x : ι) => α i) (Set.univ.{u2} ι) (fun (_x : ι) => Set.univ.{u1} (α i))) (Set.univ.{max u2 u1} (Sigma.{u2, u1} ι (fun (i_1 : ι) => α i)))
Case conversion may be inaccurate. Consider using '#align set.univ_sigma_univ Set.univ_sigma_univₓ'. -/
theorem univ_sigma_univ : ((@univ ι).Sigma fun _ => @univ (α i)) = univ :=
  ext fun _ => true_and_iff _
#align set.univ_sigma_univ Set.univ_sigma_univ

/- warning: set.sigma_univ -> Set.sigma_univ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (_x : ι) => α _x) s (fun (_x : ι) => Set.univ.{u2} (α _x))) (Set.preimage.{max u1 u2, u1} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i)) s)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (_x : ι) => α _x) s (fun (_x : ι) => Set.univ.{u1} (α _x))) (Set.preimage.{max u1 u2, u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i)) s)
Case conversion may be inaccurate. Consider using '#align set.sigma_univ Set.sigma_univₓ'. -/
@[simp]
theorem sigma_univ : s.Sigma (fun _ => univ : ∀ i, Set (α i)) = Sigma.fst ⁻¹' s :=
  ext fun _ => and_true_iff _
#align set.sigma_univ Set.sigma_univ

/- warning: set.singleton_sigma -> Set.singleton_sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {t : forall (i : ι), Set.{u2} (α i)} {i : ι}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) (Singleton.singleton.{u1, u1} ι (Set.{u1} ι) (Set.hasSingleton.{u1} ι) i) t) (Set.image.{u2, max u1 u2} (α i) (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i) (t i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {t : forall (i : ι), Set.{u1} (α i)} {i : ι} {a : α i}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) (Singleton.singleton.{u2, u2} ι (Set.{u2} ι) (Set.instSingletonSet.{u2} ι) i) t) (Set.image.{u1, max u2 u1} (α i) (Sigma.{u2, u1} ι α) (Sigma.mk.{u2, u1} ι α i) (t i))
Case conversion may be inaccurate. Consider using '#align set.singleton_sigma Set.singleton_sigmaₓ'. -/
@[simp]
theorem singleton_sigma : ({i} : Set ι).Sigma t = Sigma.mk i '' t i :=
  ext fun x => by 
    constructor
    · obtain ⟨j, a⟩ := x
      rintro ⟨rfl : j = i, ha⟩
      exact mem_image_of_mem _ ha
    · rintro ⟨b, hb, rfl⟩
      exact ⟨rfl, hb⟩
#align set.singleton_sigma Set.singleton_sigma

/- warning: set.sigma_singleton -> Set.sigma_singleton is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {a : forall (i : ι), α i}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s (fun (i : ι) => Singleton.singleton.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasSingleton.{u2} (α i)) (a i))) (Set.image.{u1, max u1 u2} ι (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (fun (i : ι) => Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i (a i)) s)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {a : forall (i : ι), α i}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s (fun (i : ι) => Singleton.singleton.{u1, u1} (α i) (Set.{u1} (α i)) (Set.instSingletonSet.{u1} (α i)) (a i))) (Set.image.{u2, max u1 u2} ι (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (fun (i : ι) => Sigma.mk.{u2, u1} ι (fun (i : ι) => α i) i (a i)) s)
Case conversion may be inaccurate. Consider using '#align set.sigma_singleton Set.sigma_singletonₓ'. -/
@[simp]
theorem sigma_singleton {a : ∀ i, α i} :
    (s.Sigma fun i => ({a i} : Set (α i))) = (fun i => Sigma.mk i <| a i) '' s := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]
#align set.sigma_singleton Set.sigma_singleton

/- warning: set.singleton_sigma_singleton -> Set.singleton_sigma_singleton is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {i : ι} {a : forall (i : ι), α i}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) (Singleton.singleton.{u1, u1} ι (Set.{u1} ι) (Set.hasSingleton.{u1} ι) i) (fun (i : ι) => Singleton.singleton.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasSingleton.{u2} (α i)) (a i))) (Singleton.singleton.{max u1 u2, max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasSingleton.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i (a i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {i : ι} {a : forall (i : ι), α i}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) (Singleton.singleton.{u2, u2} ι (Set.{u2} ι) (Set.instSingletonSet.{u2} ι) i) (fun (i : ι) => Singleton.singleton.{u1, u1} (α i) (Set.{u1} (α i)) (Set.instSingletonSet.{u1} (α i)) (a i))) (Singleton.singleton.{max u2 u1, max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instSingletonSet.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Sigma.mk.{u2, u1} ι (fun (i : ι) => α i) i (a i)))
Case conversion may be inaccurate. Consider using '#align set.singleton_sigma_singleton Set.singleton_sigma_singletonₓ'. -/
theorem singleton_sigma_singleton {a : ∀ i, α i} :
    (({i} : Set ι).Sigma fun i => ({a i} : Set (α i))) = {⟨i, a i⟩} := by
  rw [sigma_singleton, image_singleton]
#align set.singleton_sigma_singleton Set.singleton_sigma_singleton

/- warning: set.union_sigma -> Set.union_sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s₁ : Set.{u1} ι} {s₂ : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) (Union.union.{u1} (Set.{u1} ι) (Set.hasUnion.{u1} ι) s₁ s₂) t) (Union.union.{max u1 u2} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasUnion.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s₁ t) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s₂ t))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s₁ : Set.{u2} ι} {s₂ : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) (Union.union.{u2} (Set.{u2} ι) (Set.instUnionSet_1.{u2} ι) s₁ s₂) t) (Union.union.{max u2 u1} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instUnionSet_1.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s₁ t) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.union_sigma Set.union_sigmaₓ'. -/
@[simp]
theorem union_sigma : (s₁ ∪ s₂).Sigma t = s₁.Sigma t ∪ s₂.Sigma t :=
  ext fun _ => or_and_right
#align set.union_sigma Set.union_sigma

/- warning: set.sigma_union -> Set.sigma_union is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t₁ : forall (i : ι), Set.{u2} (α i)} {t₂ : forall (i : ι), Set.{u2} (α i)}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s (fun (i : ι) => Union.union.{u2} (Set.{u2} (α i)) (Set.hasUnion.{u2} (α i)) (t₁ i) (t₂ i))) (Union.union.{max u1 u2} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasUnion.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t₁) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t₂))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t₁ : forall (i : ι), Set.{u1} (α i)} {t₂ : forall (i : ι), Set.{u1} (α i)}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s (fun (i : ι) => Union.union.{u1} (Set.{u1} (α i)) (Set.instUnionSet_1.{u1} (α i)) (t₁ i) (t₂ i))) (Union.union.{max u2 u1} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instUnionSet_1.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t₁) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t₂))
Case conversion may be inaccurate. Consider using '#align set.sigma_union Set.sigma_unionₓ'. -/
@[simp]
theorem sigma_union : (s.Sigma fun i => t₁ i ∪ t₂ i) = s.Sigma t₁ ∪ s.Sigma t₂ :=
  ext fun _ => and_or_left
#align set.sigma_union Set.sigma_union

/- warning: set.sigma_inter_sigma -> Set.sigma_inter_sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s₁ : Set.{u1} ι} {s₂ : Set.{u1} ι} {t₁ : forall (i : ι), Set.{u2} (α i)} {t₂ : forall (i : ι), Set.{u2} (α i)}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasInter.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s₁ t₁) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s₂ t₂)) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) (Inter.inter.{u1} (Set.{u1} ι) (Set.hasInter.{u1} ι) s₁ s₂) (fun (i : ι) => Inter.inter.{u2} (Set.{u2} (α i)) (Set.hasInter.{u2} (α i)) (t₁ i) (t₂ i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s₁ : Set.{u2} ι} {s₂ : Set.{u2} ι} {t₁ : forall (i : ι), Set.{u1} (α i)} {t₂ : forall (i : ι), Set.{u1} (α i)}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Inter.inter.{max u2 u1} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instInterSet_1.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s₁ t₁) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s₂ t₂)) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) (Inter.inter.{u2} (Set.{u2} ι) (Set.instInterSet_1.{u2} ι) s₁ s₂) (fun (i : ι) => Inter.inter.{u1} (Set.{u1} (α i)) (Set.instInterSet_1.{u1} (α i)) (t₁ i) (t₂ i)))
Case conversion may be inaccurate. Consider using '#align set.sigma_inter_sigma Set.sigma_inter_sigmaₓ'. -/
theorem sigma_inter_sigma : s₁.Sigma t₁ ∩ s₂.Sigma t₂ = (s₁ ∩ s₂).Sigma fun i => t₁ i ∩ t₂ i := by
  ext ⟨x, y⟩
  simp [and_assoc', and_left_comm]
#align set.sigma_inter_sigma Set.sigma_inter_sigma

/- warning: set.insert_sigma -> Set.insert_sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {i : ι}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) (Insert.insert.{u1, u1} ι (Set.{u1} ι) (Set.hasInsert.{u1} ι) i s) t) (Union.union.{max u1 u2} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasUnion.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.image.{u2, max u1 u2} (α i) (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i) (t i)) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {i : ι} {a : α i}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) (Insert.insert.{u2, u2} ι (Set.{u2} ι) (Set.instInsertSet.{u2} ι) i s) t) (Union.union.{max u2 u1} (Set.{max u2 u1} (Sigma.{u2, u1} ι α)) (Set.instUnionSet_1.{max u2 u1} (Sigma.{u2, u1} ι α)) (Set.image.{u1, max u2 u1} (α i) (Sigma.{u2, u1} ι α) (Sigma.mk.{u2, u1} ι α i) (t i)) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t))
Case conversion may be inaccurate. Consider using '#align set.insert_sigma Set.insert_sigmaₓ'. -/
theorem insert_sigma : (insert i s).Sigma t = Sigma.mk i '' t i ∪ s.Sigma t := by
  rw [insert_eq, union_sigma, singleton_sigma]
#align set.insert_sigma Set.insert_sigma

/- warning: set.sigma_insert -> Set.sigma_insert is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {a : forall (i : ι), α i}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s (fun (i : ι) => Insert.insert.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasInsert.{u2} (α i)) (a i) (t i))) (Union.union.{max u1 u2} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasUnion.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.image.{u1, max u1 u2} ι (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (fun (i : ι) => Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i (a i)) s) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {a : forall (i : ι), α i}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s (fun (i : ι) => Insert.insert.{u1, u1} (α i) (Set.{u1} (α i)) (Set.instInsertSet.{u1} (α i)) (a i) (t i))) (Union.union.{max u2 u1} (Set.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instUnionSet_1.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.image.{u2, max u2 u1} ι (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (fun (i : ι) => Sigma.mk.{u2, u1} ι (fun (i : ι) => α i) i (a i)) s) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t))
Case conversion may be inaccurate. Consider using '#align set.sigma_insert Set.sigma_insertₓ'. -/
theorem sigma_insert {a : ∀ i, α i} :
    (s.Sigma fun i => insert (a i) (t i)) = (fun i => ⟨i, a i⟩) '' s ∪ s.Sigma t := by
  simp_rw [insert_eq, sigma_union, sigma_singleton]
#align set.sigma_insert Set.sigma_insert

/- warning: set.sigma_preimage_eq -> Set.sigma_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : ι -> Type.{u3}} {β : ι -> Type.{u4}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u3} (α i)} {f : ι' -> ι} {g : forall (i : ι), (β i) -> (α i)}, Eq.{succ (max u2 u4)} (Set.{max u2 u4} (Sigma.{u2, u4} ι' (fun (i : ι') => β (f i)))) (Set.Sigma.{u2, u4} ι' (fun (i : ι') => β (f i)) (Set.preimage.{u2, u1} ι' ι f s) (fun (i : ι') => Set.preimage.{u4, u3} (β (f i)) (α (f i)) (g (f i)) (t (f i)))) (Set.preimage.{max u2 u4, max u1 u3} (Sigma.{u2, u4} ι' (fun (i : ι') => β (f i))) (Sigma.{u1, u3} ι α) (fun (p : Sigma.{u2, u4} ι' (fun (i : ι') => β (f i))) => Sigma.mk.{u1, u3} ι α (f (Sigma.fst.{u2, u4} ι' (fun (i : ι') => β (f i)) p)) (g (f (Sigma.fst.{u2, u4} ι' (fun (i : ι') => β (f i)) p)) (Sigma.snd.{u2, u4} ι' (fun (i : ι') => β (f i)) p))) (Set.Sigma.{u1, u3} ι (fun (i : ι) => α i) s t))
but is expected to have type
  forall {ι : Type.{u2}} {ι' : Type.{u4}} {α : ι -> Type.{u1}} {β : ι -> Type.{u3}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {f : ι' -> ι} {g : forall (i : ι), (β i) -> (α i)}, Eq.{max (succ u4) (succ u3)} (Set.{max u3 u4} (Sigma.{u4, u3} ι' (fun (i : ι') => β (f i)))) (Set.Sigma.{u4, u3} ι' (fun (i : ι') => β (f i)) (Set.preimage.{u4, u2} ι' ι f s) (fun (i : ι') => Set.preimage.{u3, u1} (β (f i)) (α (f i)) (g (f i)) (t (f i)))) (Set.preimage.{max u4 u3, max u1 u2} (Sigma.{u4, u3} ι' (fun (i : ι') => β (f i))) (Sigma.{u2, u1} ι α) (fun (p : Sigma.{u4, u3} ι' (fun (i : ι') => β (f i))) => Sigma.mk.{u2, u1} ι α (f (Sigma.fst.{u4, u3} ι' (fun (i : ι') => β (f i)) p)) (g (f (Sigma.fst.{u4, u3} ι' (fun (i : ι') => β (f i)) p)) (Sigma.snd.{u4, u3} ι' (fun (i : ι') => β (f i)) p))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t))
Case conversion may be inaccurate. Consider using '#align set.sigma_preimage_eq Set.sigma_preimage_eqₓ'. -/
theorem sigma_preimage_eq {f : ι' → ι} {g : ∀ i, β i → α i} :
    ((f ⁻¹' s).Sigma fun i => g (f i) ⁻¹' t (f i)) =
      (fun p : Σi, β (f i) => Sigma.mk _ (g _ p.2)) ⁻¹' s.Sigma t :=
  rfl
#align set.sigma_preimage_eq Set.sigma_preimage_eq

/- warning: set.sigma_preimage_left -> Set.sigma_preimage_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : ι -> Type.{u3}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u3} (α i)} {f : ι' -> ι}, Eq.{succ (max u2 u3)} (Set.{max u2 u3} (Sigma.{u2, u3} ι' (fun (i : ι') => α (f i)))) (Set.Sigma.{u2, u3} ι' (fun (i : ι') => α (f i)) (Set.preimage.{u2, u1} ι' ι f s) (fun (i : ι') => t (f i))) (Set.preimage.{max u2 u3, max u1 u3} (Sigma.{u2, u3} ι' (fun (i : ι') => α (f i))) (Sigma.{u1, u3} ι α) (fun (p : Sigma.{u2, u3} ι' (fun (i : ι') => α (f i))) => Sigma.mk.{u1, u3} ι α (f (Sigma.fst.{u2, u3} ι' (fun (i : ι') => α (f i)) p)) (Sigma.snd.{u2, u3} ι' (fun (i : ι') => α (f i)) p)) (Set.Sigma.{u1, u3} ι (fun (i : ι) => α i) s t))
but is expected to have type
  forall {ι : Type.{u1}} {ι' : Type.{u3}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {f : ι' -> ι}, Eq.{max (succ u3) (succ u2)} (Set.{max u2 u3} (Sigma.{u3, u2} ι' (fun (i : ι') => α (f i)))) (Set.Sigma.{u3, u2} ι' (fun (i : ι') => α (f i)) (Set.preimage.{u3, u1} ι' ι f s) (fun (i : ι') => t (f i))) (Set.preimage.{max u3 u2, max u2 u1} (Sigma.{u3, u2} ι' (fun (i : ι') => α (f i))) (Sigma.{u1, u2} ι α) (fun (p : Sigma.{u3, u2} ι' (fun (i : ι') => α (f i))) => Sigma.mk.{u1, u2} ι α (f (Sigma.fst.{u3, u2} ι' (fun (i : ι') => α (f i)) p)) (Sigma.snd.{u3, u2} ι' (fun (i : ι') => α (f i)) p)) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t))
Case conversion may be inaccurate. Consider using '#align set.sigma_preimage_left Set.sigma_preimage_leftₓ'. -/
theorem sigma_preimage_left {f : ι' → ι} :
    ((f ⁻¹' s).Sigma fun i => t (f i)) = (fun p : Σi, α (f i) => Sigma.mk _ p.2) ⁻¹' s.Sigma t :=
  rfl
#align set.sigma_preimage_left Set.sigma_preimage_left

/- warning: set.sigma_preimage_right -> Set.sigma_preimage_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : ι -> Type.{u3}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {g : forall (i : ι), (β i) -> (α i)}, Eq.{succ (max u1 u3)} (Set.{max u1 u3} (Sigma.{u1, u3} ι (fun (i : ι) => β i))) (Set.Sigma.{u1, u3} ι (fun (i : ι) => β i) s (fun (i : ι) => Set.preimage.{u3, u2} (β i) (α i) (g i) (t i))) (Set.preimage.{max u1 u3, max u1 u2} (Sigma.{u1, u3} ι (fun (i : ι) => β i)) (Sigma.{u1, u2} ι α) (fun (p : Sigma.{u1, u3} ι (fun (i : ι) => β i)) => Sigma.mk.{u1, u2} ι α (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) p) (g (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) p) (Sigma.snd.{u1, u3} ι (fun (i : ι) => β i) p))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t))
but is expected to have type
  forall {ι : Type.{u3}} {α : ι -> Type.{u1}} {β : ι -> Type.{u2}} {s : Set.{u3} ι} {t : forall (i : ι), Set.{u1} (α i)} {g : forall (i : ι), (β i) -> (α i)}, Eq.{max (succ u3) (succ u2)} (Set.{max u2 u3} (Sigma.{u3, u2} ι (fun (i : ι) => β i))) (Set.Sigma.{u3, u2} ι (fun (i : ι) => β i) s (fun (i : ι) => Set.preimage.{u2, u1} (β i) (α i) (g i) (t i))) (Set.preimage.{max u3 u2, max u1 u3} (Sigma.{u3, u2} ι (fun (i : ι) => β i)) (Sigma.{u3, u1} ι α) (fun (p : Sigma.{u3, u2} ι (fun (i : ι) => β i)) => Sigma.mk.{u3, u1} ι α (Sigma.fst.{u3, u2} ι (fun (i : ι) => β i) p) (g (Sigma.fst.{u3, u2} ι (fun (i : ι) => β i) p) (Sigma.snd.{u3, u2} ι (fun (i : ι) => β i) p))) (Set.Sigma.{u3, u1} ι (fun (i : ι) => α i) s t))
Case conversion may be inaccurate. Consider using '#align set.sigma_preimage_right Set.sigma_preimage_rightₓ'. -/
theorem sigma_preimage_right {g : ∀ i, β i → α i} :
    (s.Sigma fun i => g i ⁻¹' t i) = (fun p : Σi, β i => Sigma.mk p.1 (g _ p.2)) ⁻¹' s.Sigma t :=
  rfl
#align set.sigma_preimage_right Set.sigma_preimage_right

theorem preimage_sigma_map_sigma {α' : ι' → Type _} (f : ι → ι') (g : ∀ i, α i → α' (f i))
    (s : Set ι') (t : ∀ i, Set (α' i)) :
    Sigma.map f g ⁻¹' s.Sigma t = (f ⁻¹' s).Sigma fun i => g i ⁻¹' t (f i) :=
  rfl
#align set.preimage_sigma_map_sigma Set.preimage_sigma_map_sigma

/- warning: set.mk_preimage_sigma -> Set.mk_preimage_sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {i : ι}, (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (Eq.{succ u2} (Set.{u2} (α i)) (Set.preimage.{u2, max u1 u2} (α i) (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) (t i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {i : ι}, (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (Eq.{succ u1} (Set.{u1} (α i)) (Set.preimage.{u1, max u2 u1} (α i) (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Sigma.mk.{u2, u1} ι (fun (i : ι) => α i) i) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) (t i))
Case conversion may be inaccurate. Consider using '#align set.mk_preimage_sigma Set.mk_preimage_sigmaₓ'. -/
@[simp]
theorem mk_preimage_sigma (hi : i ∈ s) : Sigma.mk i ⁻¹' s.Sigma t = t i :=
  ext fun _ => and_iff_right hi
#align set.mk_preimage_sigma Set.mk_preimage_sigma

/- warning: set.mk_preimage_sigma_eq_empty -> Set.mk_preimage_sigma_eq_empty is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {i : ι}, (Not (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s)) -> (Eq.{succ u2} (Set.{u2} (α i)) (Set.preimage.{u2, max u1 u2} (α i) (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) (EmptyCollection.emptyCollection.{u2} (Set.{u2} (α i)) (Set.hasEmptyc.{u2} (α i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {i : ι}, (Not (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s)) -> (Eq.{succ u1} (Set.{u1} (α i)) (Set.preimage.{u1, max u2 u1} (α i) (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Sigma.mk.{u2, u1} ι (fun (i : ι) => α i) i) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (α i)) (Set.instEmptyCollectionSet.{u1} (α i))))
Case conversion may be inaccurate. Consider using '#align set.mk_preimage_sigma_eq_empty Set.mk_preimage_sigma_eq_emptyₓ'. -/
@[simp]
theorem mk_preimage_sigma_eq_empty (hi : i ∉ s) : Sigma.mk i ⁻¹' s.Sigma t = ∅ :=
  ext fun _ => iff_of_false (hi ∘ And.left) id
#align set.mk_preimage_sigma_eq_empty Set.mk_preimage_sigma_eq_empty

/- warning: set.mk_preimage_sigma_eq_if -> Set.mk_preimage_sigma_eq_if is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {i : ι} [_inst_1 : DecidablePred.{succ u1} ι (fun (_x : ι) => Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) _x s)], Eq.{succ u2} (Set.{u2} (α i)) (Set.preimage.{u2, max u1 u2} (α i) (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) (ite.{succ u2} (Set.{u2} (α i)) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (_inst_1 i) (t i) (EmptyCollection.emptyCollection.{u2} (Set.{u2} (α i)) (Set.hasEmptyc.{u2} (α i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {i : ι} [_inst_1 : DecidablePred.{succ u2} ι (fun (_x : ι) => Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) _x s)], Eq.{succ u1} (Set.{u1} (α i)) (Set.preimage.{u1, max u2 u1} (α i) (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Sigma.mk.{u2, u1} ι (fun (i : ι) => α i) i) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) (ite.{succ u1} (Set.{u1} (α i)) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (_inst_1 i) (t i) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (α i)) (Set.instEmptyCollectionSet.{u1} (α i))))
Case conversion may be inaccurate. Consider using '#align set.mk_preimage_sigma_eq_if Set.mk_preimage_sigma_eq_ifₓ'. -/
theorem mk_preimage_sigma_eq_if [DecidablePred (· ∈ s)] :
    Sigma.mk i ⁻¹' s.Sigma t = if i ∈ s then t i else ∅ := by split_ifs <;> simp [h]
#align set.mk_preimage_sigma_eq_if Set.mk_preimage_sigma_eq_if

/- warning: set.mk_preimage_sigma_fn_eq_if -> Set.mk_preimage_sigma_fn_eq_if is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {i : ι} {β : Type.{u3}} [_inst_1 : DecidablePred.{succ u1} ι (fun (_x : ι) => Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) _x s)] (g : β -> (α i)), Eq.{succ u3} (Set.{u3} β) (Set.preimage.{u3, max u1 u2} β (Sigma.{u1, u2} ι (fun {i : ι} => α i)) (fun (b : β) => Sigma.mk.{u1, u2} ι (fun {i : ι} => α i) i (g b)) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) (ite.{succ u3} (Set.{u3} β) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (_inst_1 i) (Set.preimage.{u3, u2} β (α i) g (t i)) (EmptyCollection.emptyCollection.{u3} (Set.{u3} β) (Set.hasEmptyc.{u3} β)))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {i : ι} {β : Type.{u3}} [_inst_1 : DecidablePred.{succ u2} ι (fun (_x : ι) => Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) _x s)] (g : β -> (α i)), Eq.{succ u3} (Set.{u3} β) (Set.preimage.{u3, max u1 u2} β (Sigma.{u2, u1} ι α) (fun (b : β) => Sigma.mk.{u2, u1} ι α i (g b)) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) (ite.{succ u3} (Set.{u3} β) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (_inst_1 i) (Set.preimage.{u3, u1} β (α i) g (t i)) (EmptyCollection.emptyCollection.{u3} (Set.{u3} β) (Set.instEmptyCollectionSet.{u3} β)))
Case conversion may be inaccurate. Consider using '#align set.mk_preimage_sigma_fn_eq_if Set.mk_preimage_sigma_fn_eq_ifₓ'. -/
theorem mk_preimage_sigma_fn_eq_if {β : Type _} [DecidablePred (· ∈ s)] (g : β → α i) :
    (fun b => Sigma.mk i (g b)) ⁻¹' s.Sigma t = if i ∈ s then g ⁻¹' t i else ∅ :=
  ext fun _ => by split_ifs <;> simp [h]
#align set.mk_preimage_sigma_fn_eq_if Set.mk_preimage_sigma_fn_eq_if

/- warning: set.sigma_univ_range_eq -> Set.sigma_univ_range_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : ι -> Type.{u3}} {f : forall (i : ι), (α i) -> (β i)}, Eq.{succ (max u1 u3)} (Set.{max u1 u3} (Sigma.{u1, u3} ι (fun (i : ι) => β i))) (Set.Sigma.{u1, u3} ι (fun (i : ι) => β i) (Set.univ.{u1} ι) (fun (i : ι) => Set.range.{u3, succ u2} (β i) (α i) (f i))) (Set.range.{max u1 u3, max (succ u1) (succ u2)} (Sigma.{u1, u3} ι (fun (i : ι) => β i)) (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (fun (x : Sigma.{u1, u2} ι (fun (i : ι) => α i)) => Sigma.mk.{u1, u3} ι (fun (i : ι) => β i) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) x) (f (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) x) (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) x))))
but is expected to have type
  forall {ι : Type.{u3}} {α : ι -> Type.{u1}} {β : ι -> Type.{u2}} {f : forall (i : ι), (α i) -> (β i)}, Eq.{max (succ u3) (succ u2)} (Set.{max u2 u3} (Sigma.{u3, u2} ι (fun (i : ι) => β i))) (Set.Sigma.{u3, u2} ι (fun (i : ι) => β i) (Set.univ.{u3} ι) (fun (i : ι) => Set.range.{u2, succ u1} (β i) (α i) (f i))) (Set.range.{max u3 u2, max (succ u3) (succ u1)} (Sigma.{u3, u2} ι (fun (i : ι) => β i)) (Sigma.{u3, u1} ι (fun (i : ι) => α i)) (fun (x : Sigma.{u3, u1} ι (fun (i : ι) => α i)) => Sigma.mk.{u3, u2} ι (fun (i : ι) => β i) (Sigma.fst.{u3, u1} ι (fun (i : ι) => α i) x) (f (Sigma.fst.{u3, u1} ι (fun (i : ι) => α i) x) (Sigma.snd.{u3, u1} ι (fun (i : ι) => α i) x))))
Case conversion may be inaccurate. Consider using '#align set.sigma_univ_range_eq Set.sigma_univ_range_eqₓ'. -/
theorem sigma_univ_range_eq {f : ∀ i, α i → β i} :
    ((univ : Set ι).Sigma fun i => range (f i)) = range fun x : Σi, α i => ⟨x.1, f _ x.2⟩ :=
  ext <| by simp [range]
#align set.sigma_univ_range_eq Set.sigma_univ_range_eq

/- warning: set.nonempty.sigma -> Set.Nonempty.sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)}, (Set.Nonempty.{u1} ι s) -> (forall (i : ι), Set.Nonempty.{u2} (α i) (t i)) -> (Set.Nonempty.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)}, (Set.Nonempty.{u2} ι s) -> (forall (i : ι), Set.Nonempty.{u1} (α i) (t i)) -> (Set.Nonempty.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t))
Case conversion may be inaccurate. Consider using '#align set.nonempty.sigma Set.Nonempty.sigmaₓ'. -/
protected theorem Nonempty.sigma :
    s.Nonempty → (∀ i, (t i).Nonempty) → (s.Sigma t : Set _).Nonempty := fun ⟨i, hi⟩ h =>
  let ⟨a, ha⟩ := h i
  ⟨⟨i, a⟩, hi, ha⟩
#align set.nonempty.sigma Set.Nonempty.sigma

/- warning: set.nonempty.sigma_fst -> Set.Nonempty.sigma_fst is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)}, (Set.Nonempty.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) -> (Set.Nonempty.{u1} ι s)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)}, (Set.Nonempty.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) -> (Set.Nonempty.{u2} ι s)
Case conversion may be inaccurate. Consider using '#align set.nonempty.sigma_fst Set.Nonempty.sigma_fstₓ'. -/
theorem Nonempty.sigma_fst : (s.Sigma t : Set _).Nonempty → s.Nonempty := fun ⟨x, hx⟩ => ⟨x.1, hx.1⟩
#align set.nonempty.sigma_fst Set.Nonempty.sigma_fst

/- warning: set.nonempty.sigma_snd -> Set.Nonempty.sigma_snd is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)}, (Set.Nonempty.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) -> (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => Set.Nonempty.{u2} (α i) (t i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)}, (Set.Nonempty.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) -> (Exists.{succ u2} ι (fun (i : ι) => And (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (Set.Nonempty.{u1} (α i) (t i))))
Case conversion may be inaccurate. Consider using '#align set.nonempty.sigma_snd Set.Nonempty.sigma_sndₓ'. -/
theorem Nonempty.sigma_snd : (s.Sigma t : Set _).Nonempty → ∃ i ∈ s, (t i).Nonempty :=
  fun ⟨x, hx⟩ => ⟨x.1, hx.1, x.2, hx.2⟩
#align set.nonempty.sigma_snd Set.Nonempty.sigma_snd

/- warning: set.sigma_nonempty_iff -> Set.sigma_nonempty_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)}, Iff (Set.Nonempty.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => Set.Nonempty.{u2} (α i) (t i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)}, Iff (Set.Nonempty.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) (Exists.{succ u2} ι (fun (i : ι) => And (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (Set.Nonempty.{u1} (α i) (t i))))
Case conversion may be inaccurate. Consider using '#align set.sigma_nonempty_iff Set.sigma_nonempty_iffₓ'. -/
theorem sigma_nonempty_iff : (s.Sigma t : Set _).Nonempty ↔ ∃ i ∈ s, (t i).Nonempty :=
  ⟨Nonempty.sigma_snd, fun ⟨i, hi, a, ha⟩ => ⟨⟨i, a⟩, hi, ha⟩⟩
#align set.sigma_nonempty_iff Set.sigma_nonempty_iff

/- warning: set.sigma_eq_empty_iff -> Set.sigma_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)}, Iff (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t) (EmptyCollection.emptyCollection.{max u1 u2} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasEmptyc.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))))) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (Eq.{succ u2} (Set.{u2} (α i)) (t i) (EmptyCollection.emptyCollection.{u2} (Set.{u2} (α i)) (Set.hasEmptyc.{u2} (α i)))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)}, Iff (Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t) (EmptyCollection.emptyCollection.{max u2 u1} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instEmptyCollectionSet.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))))) (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (Eq.{succ u1} (Set.{u1} (α i)) (t i) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (α i)) (Set.instEmptyCollectionSet.{u1} (α i)))))
Case conversion may be inaccurate. Consider using '#align set.sigma_eq_empty_iff Set.sigma_eq_empty_iffₓ'. -/
theorem sigma_eq_empty_iff : s.Sigma t = ∅ ↔ ∀ i ∈ s, t i = ∅ :=
  not_nonempty_iff_eq_empty.symm.trans <|
    sigma_nonempty_iff.Not.trans <| by simp only [not_nonempty_iff_eq_empty, not_exists]
#align set.sigma_eq_empty_iff Set.sigma_eq_empty_iff

theorem image_sigma_mk_subset_sigma_left {a : ∀ i, α i} (ha : ∀ i, a i ∈ t i) :
    (fun i => Sigma.mk i (a i)) '' s ⊆ s.Sigma t :=
  image_subset_iff.2 fun i hi => ⟨hi, ha _⟩
#align set.image_sigma_mk_subset_sigma_left Set.image_sigma_mk_subset_sigma_left

theorem image_sigma_mk_subset_sigma_right (hi : i ∈ s) : Sigma.mk i '' t i ⊆ s.Sigma t :=
  image_subset_iff.2 fun a => And.intro hi
#align set.image_sigma_mk_subset_sigma_right Set.image_sigma_mk_subset_sigma_right

/- warning: set.sigma_subset_preimage_fst -> Set.sigma_subset_preimage_fst is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} (s : Set.{u1} ι) (t : forall (i : ι), Set.{u2} (α i)), HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasSubset.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t) (Set.preimage.{max u1 u2, u1} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i)) s)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} (s : Set.{u2} ι) (t : forall (i : ι), Set.{u1} (α i)), HasSubset.Subset.{max u2 u1} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instHasSubsetSet_1.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t) (Set.preimage.{max u2 u1, u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i)) s)
Case conversion may be inaccurate. Consider using '#align set.sigma_subset_preimage_fst Set.sigma_subset_preimage_fstₓ'. -/
theorem sigma_subset_preimage_fst (s : Set ι) (t : ∀ i, Set (α i)) : s.Sigma t ⊆ Sigma.fst ⁻¹' s :=
  fun a => And.left
#align set.sigma_subset_preimage_fst Set.sigma_subset_preimage_fst

/- warning: set.fst_image_sigma_subset -> Set.fst_image_sigma_subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} (s : Set.{u1} ι) (t : forall (i : ι), Set.{u2} (α i)), HasSubset.Subset.{u1} (Set.{u1} ι) (Set.hasSubset.{u1} ι) (Set.image.{max u1 u2, u1} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i)) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) s
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} (s : Set.{u2} ι) (t : forall (i : ι), Set.{u1} (α i)), HasSubset.Subset.{u2} (Set.{u2} ι) (Set.instHasSubsetSet_1.{u2} ι) (Set.image.{max u1 u2, u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i)) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) s
Case conversion may be inaccurate. Consider using '#align set.fst_image_sigma_subset Set.fst_image_sigma_subsetₓ'. -/
theorem fst_image_sigma_subset (s : Set ι) (t : ∀ i, Set (α i)) : Sigma.fst '' s.Sigma t ⊆ s :=
  image_subset_iff.2 fun a => And.left
#align set.fst_image_sigma_subset Set.fst_image_sigma_subset

/- warning: set.fst_image_sigma -> Set.fst_image_sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {t : forall (i : ι), Set.{u2} (α i)} (s : Set.{u1} ι), (forall (i : ι), Set.Nonempty.{u2} (α i) (t i)) -> (Eq.{succ u1} (Set.{u1} ι) (Set.image.{max u1 u2, u1} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i)) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) s)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {t : forall (i : ι), Set.{u1} (α i)} (s : Set.{u2} ι), (forall (i : ι), Set.Nonempty.{u1} (α i) (t i)) -> (Eq.{succ u2} (Set.{u2} ι) (Set.image.{max u1 u2, u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i)) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) s)
Case conversion may be inaccurate. Consider using '#align set.fst_image_sigma Set.fst_image_sigmaₓ'. -/
theorem fst_image_sigma (s : Set ι) (ht : ∀ i, (t i).Nonempty) : Sigma.fst '' s.Sigma t = s :=
  (fst_image_sigma_subset _ _).antisymm fun i hi =>
    let ⟨a, ha⟩ := ht i
    ⟨⟨i, a⟩, ⟨hi, ha⟩, rfl⟩
#align set.fst_image_sigma Set.fst_image_sigma

/- warning: set.sigma_diff_sigma -> Set.sigma_diff_sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s₁ : Set.{u1} ι} {s₂ : Set.{u1} ι} {t₁ : forall (i : ι), Set.{u2} (α i)} {t₂ : forall (i : ι), Set.{u2} (α i)}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (SDiff.sdiff.{max u1 u2} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (BooleanAlgebra.toHasSdiff.{max u1 u2} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.booleanAlgebra.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s₁ t₁) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s₂ t₂)) (Union.union.{max u1 u2} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.hasUnion.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) s₁ (SDiff.sdiff.{max u1 u2} (forall (i : ι), Set.{u2} (α i)) (Pi.hasSdiff.{u1, u2} ι (fun (i : ι) => Set.{u2} (α i)) (fun (i : ι) => BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} (α i)) (Set.booleanAlgebra.{u2} (α i)))) t₁ t₂)) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) (SDiff.sdiff.{u1} (Set.{u1} ι) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} ι) (Set.booleanAlgebra.{u1} ι)) s₁ s₂) t₁))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s₁ : Set.{u2} ι} {s₂ : Set.{u2} ι} {t₁ : forall (i : ι), Set.{u1} (α i)} {t₂ : forall (i : ι), Set.{u1} (α i)}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (SDiff.sdiff.{max u2 u1} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instSDiffSet.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s₁ t₁) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s₂ t₂)) (Union.union.{max u2 u1} (Set.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.instUnionSet_1.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) s₁ (SDiff.sdiff.{max u2 u1} (forall (i : ι), Set.{u1} (α i)) (Pi.sdiff.{u2, u1} ι (fun (i : ι) => Set.{u1} (α i)) (fun (i : ι) => Set.instSDiffSet.{u1} (α i))) t₁ t₂)) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) (SDiff.sdiff.{u2} (Set.{u2} ι) (Set.instSDiffSet.{u2} ι) s₁ s₂) t₁))
Case conversion may be inaccurate. Consider using '#align set.sigma_diff_sigma Set.sigma_diff_sigmaₓ'. -/
theorem sigma_diff_sigma : s₁.Sigma t₁ \ s₂.Sigma t₂ = s₁.Sigma (t₁ \ t₂) ∪ (s₁ \ s₂).Sigma t₁ :=
  ext fun x => by
    by_cases h₁ : x.1 ∈ s₁ <;> by_cases h₂ : x.2 ∈ t₁ x.1 <;> simp [*, ← imp_iff_or_not]
#align set.sigma_diff_sigma Set.sigma_diff_sigma

end Set

