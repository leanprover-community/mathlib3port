/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Alex Kontorovich

! This file was ported from Lean 3 source module order.filter.pi
! leanprover-community/mathlib commit 4d392a6c9c4539cbeca399b3ee0afea398fbd2eb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.Bases

/-!
# (Co)product of a family of filters

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define two filters on `Π i, α i` and prove some basic properties of these filters.

* `filter.pi (f : Π i, filter (α i))` to be the maximal filter on `Π i, α i` such that
  `∀ i, filter.tendsto (function.eval i) (filter.pi f) (f i)`. It is defined as
  `Π i, filter.comap (function.eval i) (f i)`. This is a generalization of `filter.prod` to indexed
  products.

* `filter.Coprod (f : Π i, filter (α i))`: a generalization of `filter.coprod`; it is the supremum
  of `comap (eval i) (f i)`.
-/


open Set Function

open Classical Filter

namespace Filter

variable {ι : Type _} {α : ι → Type _} {f f₁ f₂ : ∀ i, Filter (α i)} {s : ∀ i, Set (α i)}

section Pi

#print Filter.pi /-
/-- The product of an indexed family of filters. -/
def pi (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
  ⨅ i, comap (eval i) (f i)
#align filter.pi Filter.pi
-/

#print Filter.pi.isCountablyGenerated /-
instance pi.isCountablyGenerated [Countable ι] [∀ i, IsCountablyGenerated (f i)] :
    IsCountablyGenerated (pi f) :=
  infᵢ.isCountablyGenerated _
#align filter.pi.is_countably_generated Filter.pi.isCountablyGenerated
-/

#print Filter.tendsto_eval_pi /-
theorem tendsto_eval_pi (f : ∀ i, Filter (α i)) (i : ι) : Tendsto (eval i) (pi f) (f i) :=
  tendsto_infᵢ' i tendsto_comap
#align filter.tendsto_eval_pi Filter.tendsto_eval_pi
-/

/- warning: filter.tendsto_pi -> Filter.tendsto_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {β : Type.{u3}} {m : β -> (forall (i : ι), α i)} {l : Filter.{u3} β}, Iff (Filter.Tendsto.{u3, max u1 u2} β (forall (i : ι), α i) m l (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f)) (forall (i : ι), Filter.Tendsto.{u3, u2} β (α i) (fun (x : β) => m x i) l (f i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {f : forall (i : ι), Filter.{u1} (α i)} {β : Type.{u3}} {m : β -> (forall (i : ι), α i)} {l : Filter.{u3} β}, Iff (Filter.Tendsto.{u3, max u2 u1} β (forall (i : ι), α i) m l (Filter.pi.{u2, u1} ι (fun (i : ι) => α i) f)) (forall (i : ι), Filter.Tendsto.{u3, u1} β (α i) (fun (x : β) => m x i) l (f i))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_pi Filter.tendsto_piₓ'. -/
theorem tendsto_pi {β : Type _} {m : β → ∀ i, α i} {l : Filter β} :
    Tendsto m l (pi f) ↔ ∀ i, Tendsto (fun x => m x i) l (f i) := by
  simp only [pi, tendsto_infi, tendsto_comap_iff]
#align filter.tendsto_pi Filter.tendsto_pi

/- warning: filter.le_pi -> Filter.le_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {g : Filter.{max u1 u2} (forall (i : ι), α i)}, Iff (LE.le.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Preorder.toLE.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (PartialOrder.toPreorder.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.partialOrder.{max u1 u2} (forall (i : ι), α i)))) g (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f)) (forall (i : ι), Filter.Tendsto.{max u1 u2, u2} (forall (x : ι), α x) (α i) (Function.eval.{succ u1, succ u2} ι (fun (i : ι) => α i) i) g (f i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {f : forall (i : ι), Filter.{u1} (α i)} {g : Filter.{max u2 u1} (forall (i : ι), α i)}, Iff (LE.le.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Preorder.toLE.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (PartialOrder.toPreorder.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instPartialOrderFilter.{max u2 u1} (forall (i : ι), α i)))) g (Filter.pi.{u2, u1} ι (fun (i : ι) => α i) f)) (forall (i : ι), Filter.Tendsto.{max u2 u1, u1} (forall (x : ι), α x) (α i) (Function.eval.{succ u2, succ u1} ι (fun (i : ι) => α i) i) g (f i))
Case conversion may be inaccurate. Consider using '#align filter.le_pi Filter.le_piₓ'. -/
theorem le_pi {g : Filter (∀ i, α i)} : g ≤ pi f ↔ ∀ i, Tendsto (eval i) g (f i) :=
  tendsto_pi
#align filter.le_pi Filter.le_pi

/- warning: filter.pi_mono -> Filter.pi_mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f₁ : forall (i : ι), Filter.{u2} (α i)} {f₂ : forall (i : ι), Filter.{u2} (α i)}, (forall (i : ι), LE.le.{u2} (Filter.{u2} (α i)) (Preorder.toLE.{u2} (Filter.{u2} (α i)) (PartialOrder.toPreorder.{u2} (Filter.{u2} (α i)) (Filter.partialOrder.{u2} (α i)))) (f₁ i) (f₂ i)) -> (LE.le.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Preorder.toLE.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (PartialOrder.toPreorder.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.partialOrder.{max u1 u2} (forall (i : ι), α i)))) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f₁) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f₂))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f₁ : forall (i : ι), Filter.{u2} (α i)} {f₂ : forall (i : ι), Filter.{u2} (α i)}, (forall (i : ι), LE.le.{u2} (Filter.{u2} (α i)) (Preorder.toLE.{u2} (Filter.{u2} (α i)) (PartialOrder.toPreorder.{u2} (Filter.{u2} (α i)) (Filter.instPartialOrderFilter.{u2} (α i)))) (f₁ i) (f₂ i)) -> (LE.le.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Preorder.toLE.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (PartialOrder.toPreorder.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.instPartialOrderFilter.{max u1 u2} (forall (i : ι), α i)))) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f₁) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f₂))
Case conversion may be inaccurate. Consider using '#align filter.pi_mono Filter.pi_monoₓ'. -/
@[mono]
theorem pi_mono (h : ∀ i, f₁ i ≤ f₂ i) : pi f₁ ≤ pi f₂ :=
  infᵢ_mono fun i => comap_mono <| h i
#align filter.pi_mono Filter.pi_mono

#print Filter.mem_pi_of_mem /-
theorem mem_pi_of_mem (i : ι) {s : Set (α i)} (hs : s ∈ f i) : eval i ⁻¹' s ∈ pi f :=
  mem_infᵢ_of_mem i <| preimage_mem_comap hs
#align filter.mem_pi_of_mem Filter.mem_pi_of_mem
-/

/- warning: filter.pi_mem_pi -> Filter.pi_mem_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : forall (i : ι), Set.{u2} (α i)} {I : Set.{u1} ι}, (Set.Finite.{u1} ι I) -> (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) -> (Membership.Mem.{u2, u2} (Set.{u2} (α i)) (Filter.{u2} (α i)) (Filter.hasMem.{u2} (α i)) (s i) (f i))) -> (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.hasMem.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I s) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {f : forall (i : ι), Filter.{u1} (α i)} {s : forall (i : ι), Set.{u1} (α i)} {I : Set.{u2} ι}, (Set.Finite.{u2} ι I) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) -> (Membership.mem.{u1, u1} (Set.{u1} (α i)) (Filter.{u1} (α i)) (instMembershipSetFilter.{u1} (α i)) (s i) (f i))) -> (Membership.mem.{max u2 u1, max u1 u2} (Set.{max u2 u1} (forall (i : ι), α i)) (Filter.{max u2 u1} (forall (i : ι), α i)) (instMembershipSetFilter.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) I s) (Filter.pi.{u2, u1} ι (fun (i : ι) => α i) f))
Case conversion may be inaccurate. Consider using '#align filter.pi_mem_pi Filter.pi_mem_piₓ'. -/
theorem pi_mem_pi {I : Set ι} (hI : I.Finite) (h : ∀ i ∈ I, s i ∈ f i) : I.pi s ∈ pi f :=
  by
  rw [pi_def, bInter_eq_Inter]
  refine' mem_infi_of_Inter hI (fun i => _) subset.rfl
  exact preimage_mem_comap (h i i.2)
#align filter.pi_mem_pi Filter.pi_mem_pi

/- warning: filter.mem_pi -> Filter.mem_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : Set.{max u1 u2} (forall (i : ι), α i)}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.hasMem.{max u1 u2} (forall (i : ι), α i)) s (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f)) (Exists.{succ u1} (Set.{u1} ι) (fun (I : Set.{u1} ι) => And (Set.Finite.{u1} ι I) (Exists.{max (succ u1) (succ u2)} (forall (i : ι), Set.{u2} (α i)) (fun (t : forall (i : ι), Set.{u2} (α i)) => And (forall (i : ι), Membership.Mem.{u2, u2} (Set.{u2} (α i)) (Filter.{u2} (α i)) (Filter.hasMem.{u2} (α i)) (t i) (f i)) (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasSubset.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I t) s)))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {f : forall (i : ι), Filter.{u1} (α i)} {s : Set.{max u2 u1} (forall (i : ι), α i)}, Iff (Membership.mem.{max u2 u1, max u1 u2} (Set.{max u2 u1} (forall (i : ι), α i)) (Filter.{max u2 u1} (forall (i : ι), α i)) (instMembershipSetFilter.{max u2 u1} (forall (i : ι), α i)) s (Filter.pi.{u2, u1} ι (fun (i : ι) => α i) f)) (Exists.{succ u2} (Set.{u2} ι) (fun (I : Set.{u2} ι) => And (Set.Finite.{u2} ι I) (Exists.{max (succ u2) (succ u1)} (forall (i : ι), Set.{u1} (α i)) (fun (t : forall (i : ι), Set.{u1} (α i)) => And (forall (i : ι), Membership.mem.{u1, u1} (Set.{u1} (α i)) (Filter.{u1} (α i)) (instMembershipSetFilter.{u1} (α i)) (t i) (f i)) (HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instHasSubsetSet.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) I t) s)))))
Case conversion may be inaccurate. Consider using '#align filter.mem_pi Filter.mem_piₓ'. -/
theorem mem_pi {s : Set (∀ i, α i)} :
    s ∈ pi f ↔ ∃ I : Set ι, I.Finite ∧ ∃ t : ∀ i, Set (α i), (∀ i, t i ∈ f i) ∧ I.pi t ⊆ s :=
  by
  constructor
  · simp only [pi, mem_infi', mem_comap, pi_def]
    rintro ⟨I, If, V, hVf, hVI, rfl, -⟩
    choose t htf htV using hVf
    exact ⟨I, If, t, htf, Inter₂_mono fun i _ => htV i⟩
  · rintro ⟨I, If, t, htf, hts⟩
    exact mem_of_superset (pi_mem_pi If fun i _ => htf i) hts
#align filter.mem_pi Filter.mem_pi

/- warning: filter.mem_pi' -> Filter.mem_pi' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : Set.{max u1 u2} (forall (i : ι), α i)}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.hasMem.{max u1 u2} (forall (i : ι), α i)) s (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f)) (Exists.{succ u1} (Finset.{u1} ι) (fun (I : Finset.{u1} ι) => Exists.{max (succ u1) (succ u2)} (forall (i : ι), Set.{u2} (α i)) (fun (t : forall (i : ι), Set.{u2} (α i)) => And (forall (i : ι), Membership.Mem.{u2, u2} (Set.{u2} (α i)) (Filter.{u2} (α i)) (Filter.hasMem.{u2} (α i)) (t i) (f i)) (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasSubset.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) I) t) s))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {f : forall (i : ι), Filter.{u1} (α i)} {s : Set.{max u2 u1} (forall (i : ι), α i)}, Iff (Membership.mem.{max u2 u1, max u1 u2} (Set.{max u2 u1} (forall (i : ι), α i)) (Filter.{max u2 u1} (forall (i : ι), α i)) (instMembershipSetFilter.{max u2 u1} (forall (i : ι), α i)) s (Filter.pi.{u2, u1} ι (fun (i : ι) => α i) f)) (Exists.{succ u2} (Finset.{u2} ι) (fun (I : Finset.{u2} ι) => Exists.{max (succ u2) (succ u1)} (forall (i : ι), Set.{u1} (α i)) (fun (t : forall (i : ι), Set.{u1} (α i)) => And (forall (i : ι), Membership.mem.{u1, u1} (Set.{u1} (α i)) (Filter.{u1} (α i)) (instMembershipSetFilter.{u1} (α i)) (t i) (f i)) (HasSubset.Subset.{max u1 u2} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instHasSubsetSet.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Finset.toSet.{u2} ι I) t) s))))
Case conversion may be inaccurate. Consider using '#align filter.mem_pi' Filter.mem_pi'ₓ'. -/
theorem mem_pi' {s : Set (∀ i, α i)} :
    s ∈ pi f ↔ ∃ I : Finset ι, ∃ t : ∀ i, Set (α i), (∀ i, t i ∈ f i) ∧ Set.pi (↑I) t ⊆ s :=
  mem_pi.trans exists_finite_iff_finset
#align filter.mem_pi' Filter.mem_pi'

#print Filter.mem_of_pi_mem_pi /-
theorem mem_of_pi_mem_pi [∀ i, NeBot (f i)] {I : Set ι} (h : I.pi s ∈ pi f) {i : ι} (hi : i ∈ I) :
    s i ∈ f i := by
  rcases mem_pi.1 h with ⟨I', I'f, t, htf, hts⟩
  refine' mem_of_superset (htf i) fun x hx => _
  have : ∀ i, (t i).Nonempty := fun i => nonempty_of_mem (htf i)
  choose g hg
  have : update g i x ∈ I'.pi t := by
    intro j hj
    rcases eq_or_ne j i with (rfl | hne) <;> simp [*]
  simpa using hts this i hi
#align filter.mem_of_pi_mem_pi Filter.mem_of_pi_mem_pi
-/

#print Filter.pi_mem_pi_iff /-
@[simp]
theorem pi_mem_pi_iff [∀ i, NeBot (f i)] {I : Set ι} (hI : I.Finite) :
    I.pi s ∈ pi f ↔ ∀ i ∈ I, s i ∈ f i :=
  ⟨fun h i hi => mem_of_pi_mem_pi h hi, pi_mem_pi hI⟩
#align filter.pi_mem_pi_iff Filter.pi_mem_pi_iff
-/

#print Filter.hasBasis_pi /-
theorem hasBasis_pi {ι' : ι → Type} {s : ∀ i, ι' i → Set (α i)} {p : ∀ i, ι' i → Prop}
    (h : ∀ i, (f i).HasBasis (p i) (s i)) :
    (pi f).HasBasis (fun If : Set ι × ∀ i, ι' i => If.1.Finite ∧ ∀ i ∈ If.1, p i (If.2 i))
      fun If : Set ι × ∀ i, ι' i => If.1.pi fun i => s i <| If.2 i :=
  by
  have : (pi f).HasBasis _ _ := has_basis_infi' fun i => (h i).comap (eval i : (∀ j, α j) → α i)
  convert this
  ext
  simp
#align filter.has_basis_pi Filter.hasBasis_pi
-/

/- warning: filter.pi_inf_principal_univ_pi_eq_bot -> Filter.pi_inf_principal_univ_pi_eq_bot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : forall (i : ι), Set.{u2} (α i)}, Iff (Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (forall (i : ι), α i)) (HasInf.inf.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.hasInf.{max u1 u2} (forall (i : ι), α i)) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f) (Filter.principal.{max u1 u2} (forall (i : ι), α i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) s))) (Bot.bot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toHasBot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.completeLattice.{max u1 u2} (forall (i : ι), α i))))) (Exists.{succ u1} ι (fun (i : ι) => Eq.{succ u2} (Filter.{u2} (α i)) (HasInf.inf.{u2} (Filter.{u2} (α i)) (Filter.hasInf.{u2} (α i)) (f i) (Filter.principal.{u2} (α i) (s i))) (Bot.bot.{u2} (Filter.{u2} (α i)) (CompleteLattice.toHasBot.{u2} (Filter.{u2} (α i)) (Filter.completeLattice.{u2} (α i))))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {f : forall (i : ι), Filter.{u1} (α i)} {s : forall (i : ι), Set.{u1} (α i)}, Iff (Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (forall (i : ι), α i)) (HasInf.inf.{max u1 u2} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instHasInfFilter.{max u2 u1} (forall (i : ι), α i)) (Filter.pi.{u2, u1} ι (fun (i : ι) => α i) f) (Filter.principal.{max u2 u1} (forall (i : ι), α i) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) s))) (Bot.bot.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (CompleteLattice.toBot.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instCompleteLatticeFilter.{max u2 u1} (forall (i : ι), α i))))) (Exists.{succ u2} ι (fun (i : ι) => Eq.{succ u1} (Filter.{u1} (α i)) (HasInf.inf.{u1} (Filter.{u1} (α i)) (Filter.instHasInfFilter.{u1} (α i)) (f i) (Filter.principal.{u1} (α i) (s i))) (Bot.bot.{u1} (Filter.{u1} (α i)) (CompleteLattice.toBot.{u1} (Filter.{u1} (α i)) (Filter.instCompleteLatticeFilter.{u1} (α i))))))
Case conversion may be inaccurate. Consider using '#align filter.pi_inf_principal_univ_pi_eq_bot Filter.pi_inf_principal_univ_pi_eq_botₓ'. -/
@[simp]
theorem pi_inf_principal_univ_pi_eq_bot : pi f ⊓ 𝓟 (Set.pi univ s) = ⊥ ↔ ∃ i, f i ⊓ 𝓟 (s i) = ⊥ :=
  by
  constructor
  · simp only [inf_principal_eq_bot, mem_pi]
    contrapose!
    rintro (hsf : ∀ i, ∃ᶠ x in f i, x ∈ s i) I If t htf hts
    have : ∀ i, (s i ∩ t i).Nonempty := fun i => ((hsf i).and_eventually (htf i)).exists
    choose x hxs hxt
    exact hts (fun i hi => hxt i) (mem_univ_pi.2 hxs)
  · simp only [inf_principal_eq_bot]
    rintro ⟨i, hi⟩
    filter_upwards [mem_pi_of_mem i hi]with x using mt fun h => h i trivial
#align filter.pi_inf_principal_univ_pi_eq_bot Filter.pi_inf_principal_univ_pi_eq_bot

/- warning: filter.pi_inf_principal_pi_eq_bot -> Filter.pi_inf_principal_pi_eq_bot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : forall (i : ι), Set.{u2} (α i)} [_inst_1 : forall (i : ι), Filter.NeBot.{u2} (α i) (f i)] {I : Set.{u1} ι}, Iff (Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (forall (i : ι), α i)) (HasInf.inf.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.hasInf.{max u1 u2} (forall (i : ι), α i)) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f) (Filter.principal.{max u1 u2} (forall (i : ι), α i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I s))) (Bot.bot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toHasBot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.completeLattice.{max u1 u2} (forall (i : ι), α i))))) (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) => Eq.{succ u2} (Filter.{u2} (α i)) (HasInf.inf.{u2} (Filter.{u2} (α i)) (Filter.hasInf.{u2} (α i)) (f i) (Filter.principal.{u2} (α i) (s i))) (Bot.bot.{u2} (Filter.{u2} (α i)) (CompleteLattice.toHasBot.{u2} (Filter.{u2} (α i)) (Filter.completeLattice.{u2} (α i)))))))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : forall (i : ι), Set.{u2} (α i)} [_inst_1 : forall (i : ι), Filter.NeBot.{u2} (α i) (f i)] {I : Set.{u1} ι}, Iff (Eq.{max (succ u1) (succ u2)} (Filter.{max u1 u2} (forall (i : ι), α i)) (HasInf.inf.{max u2 u1} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.instHasInfFilter.{max u1 u2} (forall (i : ι), α i)) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f) (Filter.principal.{max u1 u2} (forall (i : ι), α i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I s))) (Bot.bot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toBot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.instCompleteLatticeFilter.{max u1 u2} (forall (i : ι), α i))))) (Exists.{succ u1} ι (fun (i : ι) => And (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I) (Eq.{succ u2} (Filter.{u2} (α i)) (HasInf.inf.{u2} (Filter.{u2} (α i)) (Filter.instHasInfFilter.{u2} (α i)) (f i) (Filter.principal.{u2} (α i) (s i))) (Bot.bot.{u2} (Filter.{u2} (α i)) (CompleteLattice.toBot.{u2} (Filter.{u2} (α i)) (Filter.instCompleteLatticeFilter.{u2} (α i)))))))
Case conversion may be inaccurate. Consider using '#align filter.pi_inf_principal_pi_eq_bot Filter.pi_inf_principal_pi_eq_botₓ'. -/
@[simp]
theorem pi_inf_principal_pi_eq_bot [∀ i, NeBot (f i)] {I : Set ι} :
    pi f ⊓ 𝓟 (Set.pi I s) = ⊥ ↔ ∃ i ∈ I, f i ⊓ 𝓟 (s i) = ⊥ :=
  by
  rw [← univ_pi_piecewise I, pi_inf_principal_univ_pi_eq_bot]
  refine' exists_congr fun i => _
  by_cases hi : i ∈ I <;> simp [hi, (‹∀ i, ne_bot (f i)› i).Ne]
#align filter.pi_inf_principal_pi_eq_bot Filter.pi_inf_principal_pi_eq_bot

/- warning: filter.pi_inf_principal_univ_pi_ne_bot -> Filter.pi_inf_principal_univ_pi_neBot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : forall (i : ι), Set.{u2} (α i)}, Iff (Filter.NeBot.{max u1 u2} (forall (i : ι), α i) (HasInf.inf.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.hasInf.{max u1 u2} (forall (i : ι), α i)) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f) (Filter.principal.{max u1 u2} (forall (i : ι), α i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) s)))) (forall (i : ι), Filter.NeBot.{u2} (α i) (HasInf.inf.{u2} (Filter.{u2} (α i)) (Filter.hasInf.{u2} (α i)) (f i) (Filter.principal.{u2} (α i) (s i))))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : forall (i : ι), Set.{u2} (α i)}, Iff (Filter.NeBot.{max u2 u1} (forall (i : ι), α i) (HasInf.inf.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instHasInfFilter.{max u1 u2} (forall (i : ι), α i)) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f) (Filter.principal.{max u1 u2} (forall (i : ι), α i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) s)))) (forall (i : ι), Filter.NeBot.{u2} (α i) (HasInf.inf.{u2} (Filter.{u2} (α i)) (Filter.instHasInfFilter.{u2} (α i)) (f i) (Filter.principal.{u2} (α i) (s i))))
Case conversion may be inaccurate. Consider using '#align filter.pi_inf_principal_univ_pi_ne_bot Filter.pi_inf_principal_univ_pi_neBotₓ'. -/
@[simp]
theorem pi_inf_principal_univ_pi_neBot :
    NeBot (pi f ⊓ 𝓟 (Set.pi univ s)) ↔ ∀ i, NeBot (f i ⊓ 𝓟 (s i)) := by simp [ne_bot_iff]
#align filter.pi_inf_principal_univ_pi_ne_bot Filter.pi_inf_principal_univ_pi_neBot

/- warning: filter.pi_inf_principal_pi_ne_bot -> Filter.pi_inf_principal_pi_neBot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : forall (i : ι), Set.{u2} (α i)} [_inst_1 : forall (i : ι), Filter.NeBot.{u2} (α i) (f i)] {I : Set.{u1} ι}, Iff (Filter.NeBot.{max u1 u2} (forall (i : ι), α i) (HasInf.inf.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.hasInf.{max u1 u2} (forall (i : ι), α i)) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f) (Filter.principal.{max u1 u2} (forall (i : ι), α i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I s)))) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) -> (Filter.NeBot.{u2} (α i) (HasInf.inf.{u2} (Filter.{u2} (α i)) (Filter.hasInf.{u2} (α i)) (f i) (Filter.principal.{u2} (α i) (s i)))))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : forall (i : ι), Set.{u2} (α i)} [_inst_1 : forall (i : ι), Filter.NeBot.{u2} (α i) (f i)] {I : Set.{u1} ι}, Iff (Filter.NeBot.{max u2 u1} (forall (i : ι), α i) (HasInf.inf.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instHasInfFilter.{max u1 u2} (forall (i : ι), α i)) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f) (Filter.principal.{max u1 u2} (forall (i : ι), α i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I s)))) (forall (i : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I) -> (Filter.NeBot.{u2} (α i) (HasInf.inf.{u2} (Filter.{u2} (α i)) (Filter.instHasInfFilter.{u2} (α i)) (f i) (Filter.principal.{u2} (α i) (s i)))))
Case conversion may be inaccurate. Consider using '#align filter.pi_inf_principal_pi_ne_bot Filter.pi_inf_principal_pi_neBotₓ'. -/
@[simp]
theorem pi_inf_principal_pi_neBot [∀ i, NeBot (f i)] {I : Set ι} :
    NeBot (pi f ⊓ 𝓟 (I.pi s)) ↔ ∀ i ∈ I, NeBot (f i ⊓ 𝓟 (s i)) := by simp [ne_bot_iff]
#align filter.pi_inf_principal_pi_ne_bot Filter.pi_inf_principal_pi_neBot

/- warning: filter.pi_inf_principal_pi.ne_bot -> Filter.PiInfPrincipalPi.neBot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : forall (i : ι), Set.{u2} (α i)} [h : forall (i : ι), Filter.NeBot.{u2} (α i) (HasInf.inf.{u2} (Filter.{u2} (α i)) (Filter.hasInf.{u2} (α i)) (f i) (Filter.principal.{u2} (α i) (s i)))] {I : Set.{u1} ι}, Filter.NeBot.{max u1 u2} (forall (i : ι), α i) (HasInf.inf.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.hasInf.{max u1 u2} (forall (i : ι), α i)) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f) (Filter.principal.{max u1 u2} (forall (i : ι), α i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I s)))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : forall (i : ι), Set.{u2} (α i)} [h : forall (i : ι), Filter.NeBot.{u2} (α i) (HasInf.inf.{u2} (Filter.{u2} (α i)) (Filter.instHasInfFilter.{u2} (α i)) (f i) (Filter.principal.{u2} (α i) (s i)))] {I : Set.{u1} ι}, Filter.NeBot.{max u2 u1} (forall (i : ι), α i) (HasInf.inf.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instHasInfFilter.{max u1 u2} (forall (i : ι), α i)) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f) (Filter.principal.{max u1 u2} (forall (i : ι), α i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) I s)))
Case conversion may be inaccurate. Consider using '#align filter.pi_inf_principal_pi.ne_bot Filter.PiInfPrincipalPi.neBotₓ'. -/
instance PiInfPrincipalPi.neBot [h : ∀ i, NeBot (f i ⊓ 𝓟 (s i))] {I : Set ι} :
    NeBot (pi f ⊓ 𝓟 (I.pi s)) :=
  (pi_inf_principal_univ_pi_neBot.2 ‹_›).mono <|
    inf_le_inf_left _ <| principal_mono.2 fun x hx i hi => hx i trivial
#align filter.pi_inf_principal_pi.ne_bot Filter.PiInfPrincipalPi.neBot

/- warning: filter.pi_eq_bot -> Filter.pi_eq_bot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)}, Iff (Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f) (Bot.bot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toHasBot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.completeLattice.{max u1 u2} (forall (i : ι), α i))))) (Exists.{succ u1} ι (fun (i : ι) => Eq.{succ u2} (Filter.{u2} (α i)) (f i) (Bot.bot.{u2} (Filter.{u2} (α i)) (CompleteLattice.toHasBot.{u2} (Filter.{u2} (α i)) (Filter.completeLattice.{u2} (α i))))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {f : forall (i : ι), Filter.{u1} (α i)}, Iff (Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.pi.{u2, u1} ι (fun (i : ι) => α i) f) (Bot.bot.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (CompleteLattice.toBot.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instCompleteLatticeFilter.{max u2 u1} (forall (i : ι), α i))))) (Exists.{succ u2} ι (fun (i : ι) => Eq.{succ u1} (Filter.{u1} (α i)) (f i) (Bot.bot.{u1} (Filter.{u1} (α i)) (CompleteLattice.toBot.{u1} (Filter.{u1} (α i)) (Filter.instCompleteLatticeFilter.{u1} (α i))))))
Case conversion may be inaccurate. Consider using '#align filter.pi_eq_bot Filter.pi_eq_botₓ'. -/
@[simp]
theorem pi_eq_bot : pi f = ⊥ ↔ ∃ i, f i = ⊥ := by
  simpa using @pi_inf_principal_univ_pi_eq_bot ι α f fun _ => univ
#align filter.pi_eq_bot Filter.pi_eq_bot

#print Filter.pi_neBot /-
@[simp]
theorem pi_neBot : NeBot (pi f) ↔ ∀ i, NeBot (f i) := by simp [ne_bot_iff]
#align filter.pi_ne_bot Filter.pi_neBot
-/

instance [∀ i, NeBot (f i)] : NeBot (pi f) :=
  pi_neBot.2 ‹_›

#print Filter.map_eval_pi /-
@[simp]
theorem map_eval_pi (f : ∀ i, Filter (α i)) [∀ i, NeBot (f i)] (i : ι) :
    map (eval i) (pi f) = f i :=
  by
  refine' le_antisymm (tendsto_eval_pi f i) fun s hs => _
  rcases mem_pi.1 (mem_map.1 hs) with ⟨I, hIf, t, htf, hI⟩
  rw [← image_subset_iff] at hI
  refine' mem_of_superset (htf i) ((subset_eval_image_pi _ _).trans hI)
  exact nonempty_of_mem (pi_mem_pi hIf fun i hi => htf i)
#align filter.map_eval_pi Filter.map_eval_pi
-/

/- warning: filter.pi_le_pi -> Filter.pi_le_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f₁ : forall (i : ι), Filter.{u2} (α i)} {f₂ : forall (i : ι), Filter.{u2} (α i)} [_inst_1 : forall (i : ι), Filter.NeBot.{u2} (α i) (f₁ i)], Iff (LE.le.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Preorder.toLE.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (PartialOrder.toPreorder.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.partialOrder.{max u1 u2} (forall (i : ι), α i)))) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f₁) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f₂)) (forall (i : ι), LE.le.{u2} (Filter.{u2} (α i)) (Preorder.toLE.{u2} (Filter.{u2} (α i)) (PartialOrder.toPreorder.{u2} (Filter.{u2} (α i)) (Filter.partialOrder.{u2} (α i)))) (f₁ i) (f₂ i))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f₁ : forall (i : ι), Filter.{u2} (α i)} {f₂ : forall (i : ι), Filter.{u2} (α i)} [_inst_1 : forall (i : ι), Filter.NeBot.{u2} (α i) (f₁ i)], Iff (LE.le.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Preorder.toLE.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (PartialOrder.toPreorder.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.instPartialOrderFilter.{max u1 u2} (forall (i : ι), α i)))) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f₁) (Filter.pi.{u1, u2} ι (fun (i : ι) => α i) f₂)) (forall (i : ι), LE.le.{u2} (Filter.{u2} (α i)) (Preorder.toLE.{u2} (Filter.{u2} (α i)) (PartialOrder.toPreorder.{u2} (Filter.{u2} (α i)) (Filter.instPartialOrderFilter.{u2} (α i)))) (f₁ i) (f₂ i))
Case conversion may be inaccurate. Consider using '#align filter.pi_le_pi Filter.pi_le_piₓ'. -/
@[simp]
theorem pi_le_pi [∀ i, NeBot (f₁ i)] : pi f₁ ≤ pi f₂ ↔ ∀ i, f₁ i ≤ f₂ i :=
  ⟨fun h i => map_eval_pi f₁ i ▸ (tendsto_eval_pi _ _).mono_left h, pi_mono⟩
#align filter.pi_le_pi Filter.pi_le_pi

#print Filter.pi_inj /-
@[simp]
theorem pi_inj [∀ i, NeBot (f₁ i)] : pi f₁ = pi f₂ ↔ f₁ = f₂ :=
  by
  refine' ⟨fun h => _, congr_arg pi⟩
  have hle : f₁ ≤ f₂ := pi_le_pi.1 h.le
  haveI : ∀ i, ne_bot (f₂ i) := fun i => ne_bot_of_le (hle i)
  exact hle.antisymm (pi_le_pi.1 h.ge)
#align filter.pi_inj Filter.pi_inj
-/

end Pi

/-! ### `n`-ary coproducts of filters -/


section Coprod

#print Filter.coprodᵢ /-
/-- Coproduct of filters. -/
protected def coprodᵢ (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
  ⨆ i : ι, comap (eval i) (f i)
#align filter.Coprod Filter.coprodᵢ
-/

/- warning: filter.mem_Coprod_iff -> Filter.mem_coprodᵢ_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : Set.{max u1 u2} (forall (i : ι), α i)}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.hasMem.{max u1 u2} (forall (i : ι), α i)) s (Filter.coprodᵢ.{u1, u2} ι (fun (i : ι) => α i) f)) (forall (i : ι), Exists.{succ u2} (Set.{u2} (α i)) (fun (t₁ : Set.{u2} (α i)) => Exists.{0} (Membership.Mem.{u2, u2} (Set.{u2} (α i)) (Filter.{u2} (α i)) (Filter.hasMem.{u2} (α i)) t₁ (f i)) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} (α i)) (Filter.{u2} (α i)) (Filter.hasMem.{u2} (α i)) t₁ (f i)) => HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (forall (x : ι), α x)) (Set.hasSubset.{max u1 u2} (forall (x : ι), α x)) (Set.preimage.{max u1 u2, u2} (forall (x : ι), α x) (α i) (Function.eval.{succ u1, succ u2} ι (fun (i : ι) => α i) i) t₁) s)))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {f : forall (i : ι), Filter.{u1} (α i)} {s : Set.{max u2 u1} (forall (i : ι), α i)}, Iff (Membership.mem.{max u2 u1, max u1 u2} (Set.{max u2 u1} (forall (i : ι), α i)) (Filter.{max u2 u1} (forall (i : ι), α i)) (instMembershipSetFilter.{max u2 u1} (forall (i : ι), α i)) s (Filter.coprodᵢ.{u2, u1} ι (fun (i : ι) => α i) f)) (forall (i : ι), Exists.{succ u1} (Set.{u1} (α i)) (fun (t₁ : Set.{u1} (α i)) => And (Membership.mem.{u1, u1} (Set.{u1} (α i)) (Filter.{u1} (α i)) (instMembershipSetFilter.{u1} (α i)) t₁ (f i)) (HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (forall (x : ι), α x)) (Set.instHasSubsetSet.{max u2 u1} (forall (x : ι), α x)) (Set.preimage.{max u2 u1, u1} (forall (x : ι), α x) (α i) (Function.eval.{succ u2, succ u1} ι α i) t₁) s)))
Case conversion may be inaccurate. Consider using '#align filter.mem_Coprod_iff Filter.mem_coprodᵢ_iffₓ'. -/
theorem mem_coprodᵢ_iff {s : Set (∀ i, α i)} :
    s ∈ Filter.coprodᵢ f ↔ ∀ i : ι, ∃ t₁ ∈ f i, eval i ⁻¹' t₁ ⊆ s := by simp [Filter.coprodᵢ]
#align filter.mem_Coprod_iff Filter.mem_coprodᵢ_iff

/- warning: filter.compl_mem_Coprod -> Filter.compl_mem_coprodᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {s : Set.{max u1 u2} (forall (i : ι), α i)}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.hasMem.{max u1 u2} (forall (i : ι), α i)) (HasCompl.compl.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (BooleanAlgebra.toHasCompl.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.booleanAlgebra.{max u1 u2} (forall (i : ι), α i))) s) (Filter.coprodᵢ.{u1, u2} ι (fun (i : ι) => α i) f)) (forall (i : ι), Membership.Mem.{u2, u2} (Set.{u2} (α i)) (Filter.{u2} (α i)) (Filter.hasMem.{u2} (α i)) (HasCompl.compl.{u2} (Set.{u2} (α i)) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} (α i)) (Set.booleanAlgebra.{u2} (α i))) (Set.image.{max u1 u2, u2} (forall (x : ι), α x) (α i) (Function.eval.{succ u1, succ u2} ι (fun (i : ι) => α i) i) s)) (f i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {f : forall (i : ι), Filter.{u1} (α i)} {s : Set.{max u2 u1} (forall (i : ι), α i)}, Iff (Membership.mem.{max u2 u1, max u1 u2} (Set.{max u2 u1} (forall (i : ι), α i)) (Filter.{max u2 u1} (forall (i : ι), α i)) (instMembershipSetFilter.{max u2 u1} (forall (i : ι), α i)) (HasCompl.compl.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (BooleanAlgebra.toHasCompl.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instBooleanAlgebraSet.{max u2 u1} (forall (i : ι), α i))) s) (Filter.coprodᵢ.{u2, u1} ι (fun (i : ι) => α i) f)) (forall (i : ι), Membership.mem.{u1, u1} (Set.{u1} (α i)) (Filter.{u1} (α i)) (instMembershipSetFilter.{u1} (α i)) (HasCompl.compl.{u1} (Set.{u1} (α i)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (α i)) (Set.instBooleanAlgebraSet.{u1} (α i))) (Set.image.{max u2 u1, u1} (forall (x : ι), α x) (α i) (Function.eval.{succ u2, succ u1} ι (fun (i : ι) => α i) i) s)) (f i))
Case conversion may be inaccurate. Consider using '#align filter.compl_mem_Coprod Filter.compl_mem_coprodᵢₓ'. -/
theorem compl_mem_coprodᵢ {s : Set (∀ i, α i)} :
    sᶜ ∈ Filter.coprodᵢ f ↔ ∀ i, (eval i '' s)ᶜ ∈ f i := by
  simp only [Filter.coprodᵢ, mem_supr, compl_mem_comap]
#align filter.compl_mem_Coprod Filter.compl_mem_coprodᵢ

#print Filter.coprodᵢ_neBot_iff' /-
theorem coprodᵢ_neBot_iff' : NeBot (Filter.coprodᵢ f) ↔ (∀ i, Nonempty (α i)) ∧ ∃ d, NeBot (f d) :=
  by simp only [Filter.coprodᵢ, supr_ne_bot, ← exists_and_left, ← comap_eval_ne_bot_iff']
#align filter.Coprod_ne_bot_iff' Filter.coprodᵢ_neBot_iff'
-/

#print Filter.coprodᵢ_neBot_iff /-
@[simp]
theorem coprodᵢ_neBot_iff [∀ i, Nonempty (α i)] : NeBot (Filter.coprodᵢ f) ↔ ∃ d, NeBot (f d) := by
  simp [Coprod_ne_bot_iff', *]
#align filter.Coprod_ne_bot_iff Filter.coprodᵢ_neBot_iff
-/

/- warning: filter.Coprod_eq_bot_iff' -> Filter.coprodᵢ_eq_bot_iff' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)}, Iff (Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.coprodᵢ.{u1, u2} ι (fun (i : ι) => α i) f) (Bot.bot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toHasBot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.completeLattice.{max u1 u2} (forall (i : ι), α i))))) (Or (Exists.{succ u1} ι (fun (i : ι) => IsEmpty.{succ u2} (α i))) (Eq.{max (succ u1) (succ u2)} (forall (i : ι), Filter.{u2} (α i)) f (Bot.bot.{max u1 u2} (forall (i : ι), Filter.{u2} (α i)) (Pi.hasBot.{u1, u2} ι (fun (i : ι) => Filter.{u2} (α i)) (fun (i : ι) => CompleteLattice.toHasBot.{u2} (Filter.{u2} (α i)) (Filter.completeLattice.{u2} (α i)))))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {f : forall (i : ι), Filter.{u1} (α i)}, Iff (Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.coprodᵢ.{u2, u1} ι (fun (i : ι) => α i) f) (Bot.bot.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (CompleteLattice.toBot.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instCompleteLatticeFilter.{max u2 u1} (forall (i : ι), α i))))) (Or (Exists.{succ u2} ι (fun (i : ι) => IsEmpty.{succ u1} (α i))) (Eq.{max (succ u2) (succ u1)} (forall (i : ι), Filter.{u1} (α i)) f (Bot.bot.{max u2 u1} (forall (i : ι), Filter.{u1} (α i)) (Pi.instBotForAll.{u2, u1} ι (fun (i : ι) => Filter.{u1} (α i)) (fun (i : ι) => CompleteLattice.toBot.{u1} (Filter.{u1} (α i)) (Filter.instCompleteLatticeFilter.{u1} (α i)))))))
Case conversion may be inaccurate. Consider using '#align filter.Coprod_eq_bot_iff' Filter.coprodᵢ_eq_bot_iff'ₓ'. -/
theorem coprodᵢ_eq_bot_iff' : Filter.coprodᵢ f = ⊥ ↔ (∃ i, IsEmpty (α i)) ∨ f = ⊥ := by
  simpa [not_and_or, funext_iff] using not_congr Coprod_ne_bot_iff'
#align filter.Coprod_eq_bot_iff' Filter.coprodᵢ_eq_bot_iff'

/- warning: filter.Coprod_eq_bot_iff -> Filter.coprodᵢ_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} [_inst_1 : forall (i : ι), Nonempty.{succ u2} (α i)], Iff (Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.coprodᵢ.{u1, u2} ι (fun (i : ι) => α i) f) (Bot.bot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toHasBot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.completeLattice.{max u1 u2} (forall (i : ι), α i))))) (Eq.{max (succ u1) (succ u2)} (forall (i : ι), Filter.{u2} (α i)) f (Bot.bot.{max u1 u2} (forall (i : ι), Filter.{u2} (α i)) (Pi.hasBot.{u1, u2} ι (fun (i : ι) => Filter.{u2} (α i)) (fun (i : ι) => CompleteLattice.toHasBot.{u2} (Filter.{u2} (α i)) (Filter.completeLattice.{u2} (α i))))))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} [_inst_1 : forall (i : ι), Nonempty.{succ u2} (α i)], Iff (Eq.{max (succ u1) (succ u2)} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.coprodᵢ.{u1, u2} ι (fun (i : ι) => α i) f) (Bot.bot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toBot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.instCompleteLatticeFilter.{max u1 u2} (forall (i : ι), α i))))) (Eq.{max (succ u1) (succ u2)} (forall (i : ι), Filter.{u2} (α i)) f (Bot.bot.{max u1 u2} (forall (i : ι), Filter.{u2} (α i)) (Pi.instBotForAll.{u1, u2} ι (fun (i : ι) => Filter.{u2} (α i)) (fun (i : ι) => CompleteLattice.toBot.{u2} (Filter.{u2} (α i)) (Filter.instCompleteLatticeFilter.{u2} (α i))))))
Case conversion may be inaccurate. Consider using '#align filter.Coprod_eq_bot_iff Filter.coprodᵢ_eq_bot_iffₓ'. -/
@[simp]
theorem coprodᵢ_eq_bot_iff [∀ i, Nonempty (α i)] : Filter.coprodᵢ f = ⊥ ↔ f = ⊥ := by
  simpa [funext_iff] using not_congr Coprod_ne_bot_iff
#align filter.Coprod_eq_bot_iff Filter.coprodᵢ_eq_bot_iff

/- warning: filter.Coprod_bot' -> Filter.coprodᵢ_bot' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}}, Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.coprodᵢ.{u1, u2} ι (fun (i : ι) => α i) (Bot.bot.{max u1 u2} (forall (i : ι), Filter.{u2} (α i)) (Pi.hasBot.{u1, u2} ι (fun (i : ι) => Filter.{u2} (α i)) (fun (i : ι) => CompleteLattice.toHasBot.{u2} (Filter.{u2} (α i)) (Filter.completeLattice.{u2} (α i)))))) (Bot.bot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toHasBot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.completeLattice.{max u1 u2} (forall (i : ι), α i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.coprodᵢ.{u2, u1} ι (fun (i : ι) => α i) (Bot.bot.{max u2 u1} (forall (i : ι), Filter.{u1} (α i)) (Pi.instBotForAll.{u2, u1} ι (fun (i : ι) => Filter.{u1} (α i)) (fun (i : ι) => CompleteLattice.toBot.{u1} (Filter.{u1} (α i)) (Filter.instCompleteLatticeFilter.{u1} (α i)))))) (Bot.bot.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (CompleteLattice.toBot.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instCompleteLatticeFilter.{max u2 u1} (forall (i : ι), α i))))
Case conversion may be inaccurate. Consider using '#align filter.Coprod_bot' Filter.coprodᵢ_bot'ₓ'. -/
@[simp]
theorem coprodᵢ_bot' : Filter.coprodᵢ (⊥ : ∀ i, Filter (α i)) = ⊥ :=
  coprodᵢ_eq_bot_iff'.2 (Or.inr rfl)
#align filter.Coprod_bot' Filter.coprodᵢ_bot'

/- warning: filter.Coprod_bot -> Filter.coprodᵢ_bot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}}, Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.coprodᵢ.{u1, u2} ι (fun (_x : ι) => α _x) (fun (_x : ι) => Bot.bot.{u2} (Filter.{u2} (α _x)) (CompleteLattice.toHasBot.{u2} (Filter.{u2} (α _x)) (Filter.completeLattice.{u2} (α _x))))) (Bot.bot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (CompleteLattice.toHasBot.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.completeLattice.{max u1 u2} (forall (i : ι), α i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.coprodᵢ.{u2, u1} ι (fun (_x : ι) => α _x) (fun (_x : ι) => Bot.bot.{u1} (Filter.{u1} (α _x)) (CompleteLattice.toBot.{u1} (Filter.{u1} (α _x)) (Filter.instCompleteLatticeFilter.{u1} (α _x))))) (Bot.bot.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (CompleteLattice.toBot.{max u2 u1} (Filter.{max u2 u1} (forall (i : ι), α i)) (Filter.instCompleteLatticeFilter.{max u2 u1} (forall (i : ι), α i))))
Case conversion may be inaccurate. Consider using '#align filter.Coprod_bot Filter.coprodᵢ_botₓ'. -/
@[simp]
theorem coprodᵢ_bot : Filter.coprodᵢ (fun _ => ⊥ : ∀ i, Filter (α i)) = ⊥ :=
  coprodᵢ_bot'
#align filter.Coprod_bot Filter.coprodᵢ_bot

#print Filter.NeBot.coprodᵢ /-
theorem NeBot.coprodᵢ [∀ i, Nonempty (α i)] {i : ι} (h : NeBot (f i)) : NeBot (Filter.coprodᵢ f) :=
  coprodᵢ_neBot_iff.2 ⟨i, h⟩
#align filter.ne_bot.Coprod Filter.NeBot.coprodᵢ
-/

#print Filter.coprodᵢ_neBot /-
@[instance]
theorem coprodᵢ_neBot [∀ i, Nonempty (α i)] [Nonempty ι] (f : ∀ i, Filter (α i))
    [H : ∀ i, NeBot (f i)] : NeBot (Filter.coprodᵢ f) :=
  (H (Classical.arbitrary ι)).coprodᵢ
#align filter.Coprod_ne_bot Filter.coprodᵢ_neBot
-/

/- warning: filter.Coprod_mono -> Filter.coprodᵢ_mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f₁ : forall (i : ι), Filter.{u2} (α i)} {f₂ : forall (i : ι), Filter.{u2} (α i)}, (forall (i : ι), LE.le.{u2} (Filter.{u2} (α i)) (Preorder.toLE.{u2} (Filter.{u2} (α i)) (PartialOrder.toPreorder.{u2} (Filter.{u2} (α i)) (Filter.partialOrder.{u2} (α i)))) (f₁ i) (f₂ i)) -> (LE.le.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Preorder.toLE.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (PartialOrder.toPreorder.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.partialOrder.{max u1 u2} (forall (i : ι), α i)))) (Filter.coprodᵢ.{u1, u2} ι (fun (i : ι) => α i) f₁) (Filter.coprodᵢ.{u1, u2} ι (fun (i : ι) => α i) f₂))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f₁ : forall (i : ι), Filter.{u2} (α i)} {f₂ : forall (i : ι), Filter.{u2} (α i)}, (forall (i : ι), LE.le.{u2} (Filter.{u2} (α i)) (Preorder.toLE.{u2} (Filter.{u2} (α i)) (PartialOrder.toPreorder.{u2} (Filter.{u2} (α i)) (Filter.instPartialOrderFilter.{u2} (α i)))) (f₁ i) (f₂ i)) -> (LE.le.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Preorder.toLE.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (PartialOrder.toPreorder.{max u1 u2} (Filter.{max u1 u2} (forall (i : ι), α i)) (Filter.instPartialOrderFilter.{max u1 u2} (forall (i : ι), α i)))) (Filter.coprodᵢ.{u1, u2} ι (fun (i : ι) => α i) f₁) (Filter.coprodᵢ.{u1, u2} ι (fun (i : ι) => α i) f₂))
Case conversion may be inaccurate. Consider using '#align filter.Coprod_mono Filter.coprodᵢ_monoₓ'. -/
@[mono]
theorem coprodᵢ_mono (hf : ∀ i, f₁ i ≤ f₂ i) : Filter.coprodᵢ f₁ ≤ Filter.coprodᵢ f₂ :=
  supᵢ_mono fun i => comap_mono (hf i)
#align filter.Coprod_mono Filter.coprodᵢ_mono

variable {β : ι → Type _} {m : ∀ i, α i → β i}

/- warning: filter.map_pi_map_Coprod_le -> Filter.map_pi_map_coprodᵢ_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {f : forall (i : ι), Filter.{u2} (α i)} {β : ι -> Type.{u3}} {m : forall (i : ι), (α i) -> (β i)}, LE.le.{max u1 u3} (Filter.{max u1 u3} (forall (i : ι), β i)) (Preorder.toLE.{max u1 u3} (Filter.{max u1 u3} (forall (i : ι), β i)) (PartialOrder.toPreorder.{max u1 u3} (Filter.{max u1 u3} (forall (i : ι), β i)) (Filter.partialOrder.{max u1 u3} (forall (i : ι), β i)))) (Filter.map.{max u1 u2, max u1 u3} (forall (i : ι), α i) (forall (i : ι), β i) (fun (k : forall (i : ι), α i) (i : ι) => m i (k i)) (Filter.coprodᵢ.{u1, u2} ι (fun (i : ι) => α i) f)) (Filter.coprodᵢ.{u1, u3} ι (fun (i : ι) => β i) (fun (i : ι) => Filter.map.{u2, u3} (α i) (β i) (m i) (f i)))
but is expected to have type
  forall {ι : Type.{u3}} {α : ι -> Type.{u1}} {f : forall (i : ι), Filter.{u1} (α i)} {β : ι -> Type.{u2}} {m : forall (i : ι), (α i) -> (β i)}, LE.le.{max u3 u2} (Filter.{max u3 u2} (forall (i : ι), β i)) (Preorder.toLE.{max u3 u2} (Filter.{max u3 u2} (forall (i : ι), β i)) (PartialOrder.toPreorder.{max u3 u2} (Filter.{max u3 u2} (forall (i : ι), β i)) (Filter.instPartialOrderFilter.{max u3 u2} (forall (i : ι), β i)))) (Filter.map.{max u3 u1, max u3 u2} (forall (i : ι), α i) (forall (i : ι), β i) (fun (k : forall (i : ι), α i) (i : ι) => m i (k i)) (Filter.coprodᵢ.{u3, u1} ι (fun (i : ι) => α i) f)) (Filter.coprodᵢ.{u3, u2} ι (fun (i : ι) => β i) (fun (i : ι) => Filter.map.{u1, u2} (α i) (β i) (m i) (f i)))
Case conversion may be inaccurate. Consider using '#align filter.map_pi_map_Coprod_le Filter.map_pi_map_coprodᵢ_leₓ'. -/
theorem map_pi_map_coprodᵢ_le :
    map (fun k : ∀ i, α i => fun i => m i (k i)) (Filter.coprodᵢ f) ≤
      Filter.coprodᵢ fun i => map (m i) (f i) :=
  by
  simp only [le_def, mem_map, mem_Coprod_iff]
  intro s h i
  obtain ⟨t, H, hH⟩ := h i
  exact ⟨{ x : α i | m i x ∈ t }, H, fun x hx => hH hx⟩
#align filter.map_pi_map_Coprod_le Filter.map_pi_map_coprodᵢ_le

#print Filter.Tendsto.pi_map_coprodᵢ /-
theorem Tendsto.pi_map_coprodᵢ {g : ∀ i, Filter (β i)} (h : ∀ i, Tendsto (m i) (f i) (g i)) :
    Tendsto (fun k : ∀ i, α i => fun i => m i (k i)) (Filter.coprodᵢ f) (Filter.coprodᵢ g) :=
  map_pi_map_coprodᵢ_le.trans (coprodᵢ_mono h)
#align filter.tendsto.pi_map_Coprod Filter.Tendsto.pi_map_coprodᵢ
-/

end Coprod

end Filter

