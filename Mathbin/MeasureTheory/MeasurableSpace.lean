/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module measure_theory.measurable_space
! leanprover-community/mathlib commit 3905fa80e62c0898131285baab35559fbc4e5cda
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Prod.Tprod
import Mathbin.GroupTheory.Coset
import Mathbin.Logic.Equiv.Fin
import Mathbin.MeasureTheory.MeasurableSpaceDef
import Mathbin.Order.Filter.SmallSets
import Mathbin.Order.LiminfLimsup
import Mathbin.MeasureTheory.Tactic

/-!
# Measurable spaces and measurable functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides properties of measurable spaces and the functions and isomorphisms
between them. The definition of a measurable space is in `measure_theory.measurable_space_def`.

A measurable space is a set equipped with a σ-algebra, a collection of
subsets closed under complementation and countable union. A function
between measurable spaces is measurable if the preimage of each
measurable subset is measurable.

σ-algebras on a fixed set `α` form a complete lattice. Here we order
σ-algebras by writing `m₁ ≤ m₂` if every set which is `m₁`-measurable is
also `m₂`-measurable (that is, `m₁` is a subset of `m₂`). In particular, any
collection of subsets of `α` generates a smallest σ-algebra which
contains all of them. A function `f : α → β` induces a Galois connection
between the lattices of σ-algebras on `α` and `β`.

A measurable equivalence between measurable spaces is an equivalence
which respects the σ-algebras, that is, for which both directions of
the equivalence are measurable functions.

We say that a filter `f` is measurably generated if every set `s ∈ f` includes a measurable
set `t ∈ f`. This property is useful, e.g., to extract a measurable witness of `filter.eventually`.

## Notation

* We write `α ≃ᵐ β` for measurable equivalences between the measurable spaces `α` and `β`.
  This should not be confused with `≃ₘ` which is used for diffeomorphisms between manifolds.

## Implementation notes

Measurability of a function `f : α → β` between measurable spaces is
defined in terms of the Galois connection induced by f.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function, measurable equivalence, dynkin system,
π-λ theorem, π-system
-/


open Set Encodable Function Equiv

open Filter MeasureTheory

variable {α β γ δ δ' : Type _} {ι : Sort _} {s t u : Set α}

namespace MeasurableSpace

section Functors

variable {m m₁ m₂ : MeasurableSpace α} {m' : MeasurableSpace β} {f : α → β} {g : β → α}

#print MeasurableSpace.map /-
/-- The forward image of a measurable space under a function. `map f m` contains the sets
  `s : set β` whose preimage under `f` is measurable. -/
protected def map (f : α → β) (m : MeasurableSpace α) : MeasurableSpace β
    where
  MeasurableSet' s := measurable_set[m] <| f ⁻¹' s
  measurable_set_empty := m.measurable_set_empty
  measurable_set_compl s hs := m.measurable_set_compl _ hs
  measurable_set_iUnion f hf := by
    rw [preimage_Union]
    exact m.measurable_set_Union _ hf
#align measurable_space.map MeasurableSpace.map
-/

#print MeasurableSpace.map_id /-
@[simp]
theorem map_id : m.map id = m :=
  MeasurableSpace.ext fun s => Iff.rfl
#align measurable_space.map_id MeasurableSpace.map_id
-/

#print MeasurableSpace.map_comp /-
@[simp]
theorem map_comp {f : α → β} {g : β → γ} : (m.map f).map g = m.map (g ∘ f) :=
  MeasurableSpace.ext fun s => Iff.rfl
#align measurable_space.map_comp MeasurableSpace.map_comp
-/

#print MeasurableSpace.comap /-
/-- The reverse image of a measurable space under a function. `comap f m` contains the sets
  `s : set α` such that `s` is the `f`-preimage of a measurable set in `β`. -/
protected def comap (f : α → β) (m : MeasurableSpace β) : MeasurableSpace α
    where
  MeasurableSet' s := ∃ s', measurable_set[m] s' ∧ f ⁻¹' s' = s
  measurable_set_empty := ⟨∅, m.measurable_set_empty, rfl⟩
  measurable_set_compl := fun s ⟨s', h₁, h₂⟩ => ⟨s'ᶜ, m.measurable_set_compl _ h₁, h₂ ▸ rfl⟩
  measurable_set_iUnion s hs :=
    let ⟨s', hs'⟩ := Classical.axiom_of_choice hs
    ⟨⋃ i, s' i, m.measurable_set_iUnion _ fun i => (hs' i).left, by simp [hs']⟩
#align measurable_space.comap MeasurableSpace.comap
-/

#print MeasurableSpace.comap_eq_generateFrom /-
theorem comap_eq_generateFrom (m : MeasurableSpace β) (f : α → β) :
    m.comap f = generateFrom { t | ∃ s, MeasurableSet s ∧ f ⁻¹' s = t } := by
  convert generate_from_measurable_set.symm
#align measurable_space.comap_eq_generate_from MeasurableSpace.comap_eq_generateFrom
-/

#print MeasurableSpace.comap_id /-
@[simp]
theorem comap_id : m.comap id = m :=
  MeasurableSpace.ext fun s => ⟨fun ⟨s', hs', h⟩ => h ▸ hs', fun h => ⟨s, h, rfl⟩⟩
#align measurable_space.comap_id MeasurableSpace.comap_id
-/

#print MeasurableSpace.comap_comp /-
@[simp]
theorem comap_comp {f : β → α} {g : γ → β} : (m.comap f).comap g = m.comap (f ∘ g) :=
  MeasurableSpace.ext fun s =>
    ⟨fun ⟨t, ⟨u, h, hu⟩, ht⟩ => ⟨u, h, ht ▸ hu ▸ rfl⟩, fun ⟨t, h, ht⟩ => ⟨f ⁻¹' t, ⟨_, h, rfl⟩, ht⟩⟩
#align measurable_space.comap_comp MeasurableSpace.comap_comp
-/

/- warning: measurable_space.comap_le_iff_le_map -> MeasurableSpace.comap_le_iff_le_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {m' : MeasurableSpace.{u2} β} {f : α -> β}, Iff (LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) (MeasurableSpace.comap.{u1, u2} α β f m') m) (LE.le.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.hasLe.{u2} β) m' (MeasurableSpace.map.{u1, u2} α β f m))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {m' : MeasurableSpace.{u1} β} {f : α -> β}, Iff (LE.le.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instLEMeasurableSpace.{u2} α) (MeasurableSpace.comap.{u2, u1} α β f m') m) (LE.le.{u1} (MeasurableSpace.{u1} β) (MeasurableSpace.instLEMeasurableSpace.{u1} β) m' (MeasurableSpace.map.{u2, u1} α β f m))
Case conversion may be inaccurate. Consider using '#align measurable_space.comap_le_iff_le_map MeasurableSpace.comap_le_iff_le_mapₓ'. -/
theorem comap_le_iff_le_map {f : α → β} : m'.comap f ≤ m ↔ m' ≤ m.map f :=
  ⟨fun h s hs => h _ ⟨_, hs, rfl⟩, fun h s ⟨t, ht, HEq⟩ => HEq ▸ h _ ht⟩
#align measurable_space.comap_le_iff_le_map MeasurableSpace.comap_le_iff_le_map

/- warning: measurable_space.gc_comap_map -> MeasurableSpace.gc_comap_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), GaloisConnection.{u2, u1} (MeasurableSpace.{u2} β) (MeasurableSpace.{u1} α) (PartialOrder.toPreorder.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.partialOrder.{u2} β)) (PartialOrder.toPreorder.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.partialOrder.{u1} α)) (MeasurableSpace.comap.{u1, u2} α β f) (MeasurableSpace.map.{u1, u2} α β f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), GaloisConnection.{u2, u1} (MeasurableSpace.{u2} β) (MeasurableSpace.{u1} α) (PartialOrder.toPreorder.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.instPartialOrderMeasurableSpace.{u2} β)) (PartialOrder.toPreorder.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instPartialOrderMeasurableSpace.{u1} α)) (MeasurableSpace.comap.{u1, u2} α β f) (MeasurableSpace.map.{u1, u2} α β f)
Case conversion may be inaccurate. Consider using '#align measurable_space.gc_comap_map MeasurableSpace.gc_comap_mapₓ'. -/
theorem gc_comap_map (f : α → β) :
    GaloisConnection (MeasurableSpace.comap f) (MeasurableSpace.map f) := fun f g =>
  comap_le_iff_le_map
#align measurable_space.gc_comap_map MeasurableSpace.gc_comap_map

/- warning: measurable_space.map_mono -> MeasurableSpace.map_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m₁ : MeasurableSpace.{u1} α} {m₂ : MeasurableSpace.{u1} α} {f : α -> β}, (LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) m₁ m₂) -> (LE.le.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.hasLe.{u2} β) (MeasurableSpace.map.{u1, u2} α β f m₁) (MeasurableSpace.map.{u1, u2} α β f m₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m₁ : MeasurableSpace.{u2} α} {m₂ : MeasurableSpace.{u2} α} {f : α -> β}, (LE.le.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instLEMeasurableSpace.{u2} α) m₁ m₂) -> (LE.le.{u1} (MeasurableSpace.{u1} β) (MeasurableSpace.instLEMeasurableSpace.{u1} β) (MeasurableSpace.map.{u2, u1} α β f m₁) (MeasurableSpace.map.{u2, u1} α β f m₂))
Case conversion may be inaccurate. Consider using '#align measurable_space.map_mono MeasurableSpace.map_monoₓ'. -/
theorem map_mono (h : m₁ ≤ m₂) : m₁.map f ≤ m₂.map f :=
  (gc_comap_map f).monotone_u h
#align measurable_space.map_mono MeasurableSpace.map_mono

/- warning: measurable_space.monotone_map -> MeasurableSpace.monotone_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, Monotone.{u1, u2} (MeasurableSpace.{u1} α) (MeasurableSpace.{u2} β) (PartialOrder.toPreorder.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.partialOrder.{u1} α)) (PartialOrder.toPreorder.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.partialOrder.{u2} β)) (MeasurableSpace.map.{u1, u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, Monotone.{u2, u1} (MeasurableSpace.{u2} α) (MeasurableSpace.{u1} β) (PartialOrder.toPreorder.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instPartialOrderMeasurableSpace.{u2} α)) (PartialOrder.toPreorder.{u1} (MeasurableSpace.{u1} β) (MeasurableSpace.instPartialOrderMeasurableSpace.{u1} β)) (MeasurableSpace.map.{u2, u1} α β f)
Case conversion may be inaccurate. Consider using '#align measurable_space.monotone_map MeasurableSpace.monotone_mapₓ'. -/
theorem monotone_map : Monotone (MeasurableSpace.map f) := fun a b h => map_mono h
#align measurable_space.monotone_map MeasurableSpace.monotone_map

/- warning: measurable_space.comap_mono -> MeasurableSpace.comap_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m₁ : MeasurableSpace.{u1} α} {m₂ : MeasurableSpace.{u1} α} {g : β -> α}, (LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) m₁ m₂) -> (LE.le.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.hasLe.{u2} β) (MeasurableSpace.comap.{u2, u1} β α g m₁) (MeasurableSpace.comap.{u2, u1} β α g m₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m₁ : MeasurableSpace.{u2} α} {m₂ : MeasurableSpace.{u2} α} {g : β -> α}, (LE.le.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instLEMeasurableSpace.{u2} α) m₁ m₂) -> (LE.le.{u1} (MeasurableSpace.{u1} β) (MeasurableSpace.instLEMeasurableSpace.{u1} β) (MeasurableSpace.comap.{u1, u2} β α g m₁) (MeasurableSpace.comap.{u1, u2} β α g m₂))
Case conversion may be inaccurate. Consider using '#align measurable_space.comap_mono MeasurableSpace.comap_monoₓ'. -/
theorem comap_mono (h : m₁ ≤ m₂) : m₁.comap g ≤ m₂.comap g :=
  (gc_comap_map g).monotone_l h
#align measurable_space.comap_mono MeasurableSpace.comap_mono

/- warning: measurable_space.monotone_comap -> MeasurableSpace.monotone_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {g : β -> α}, Monotone.{u1, u2} (MeasurableSpace.{u1} α) (MeasurableSpace.{u2} β) (PartialOrder.toPreorder.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.partialOrder.{u1} α)) (PartialOrder.toPreorder.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.partialOrder.{u2} β)) (MeasurableSpace.comap.{u2, u1} β α g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {g : β -> α}, Monotone.{u2, u1} (MeasurableSpace.{u2} α) (MeasurableSpace.{u1} β) (PartialOrder.toPreorder.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instPartialOrderMeasurableSpace.{u2} α)) (PartialOrder.toPreorder.{u1} (MeasurableSpace.{u1} β) (MeasurableSpace.instPartialOrderMeasurableSpace.{u1} β)) (MeasurableSpace.comap.{u1, u2} β α g)
Case conversion may be inaccurate. Consider using '#align measurable_space.monotone_comap MeasurableSpace.monotone_comapₓ'. -/
theorem monotone_comap : Monotone (MeasurableSpace.comap g) := fun a b h => comap_mono h
#align measurable_space.monotone_comap MeasurableSpace.monotone_comap

/- warning: measurable_space.comap_bot -> MeasurableSpace.comap_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {g : β -> α}, Eq.{succ u2} (MeasurableSpace.{u2} β) (MeasurableSpace.comap.{u2, u1} β α g (Bot.bot.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toHasBot.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.completeLattice.{u1} α)))) (Bot.bot.{u2} (MeasurableSpace.{u2} β) (CompleteLattice.toHasBot.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.completeLattice.{u2} β)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {g : β -> α}, Eq.{succ u2} (MeasurableSpace.{u2} β) (MeasurableSpace.comap.{u2, u1} β α g (Bot.bot.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toBot.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u1} α)))) (Bot.bot.{u2} (MeasurableSpace.{u2} β) (CompleteLattice.toBot.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u2} β)))
Case conversion may be inaccurate. Consider using '#align measurable_space.comap_bot MeasurableSpace.comap_botₓ'. -/
@[simp]
theorem comap_bot : (⊥ : MeasurableSpace α).comap g = ⊥ :=
  (gc_comap_map g).l_bot
#align measurable_space.comap_bot MeasurableSpace.comap_bot

/- warning: measurable_space.comap_sup -> MeasurableSpace.comap_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m₁ : MeasurableSpace.{u1} α} {m₂ : MeasurableSpace.{u1} α} {g : β -> α}, Eq.{succ u2} (MeasurableSpace.{u2} β) (MeasurableSpace.comap.{u2, u1} β α g (Sup.sup.{u1} (MeasurableSpace.{u1} α) (SemilatticeSup.toHasSup.{u1} (MeasurableSpace.{u1} α) (Lattice.toSemilatticeSup.{u1} (MeasurableSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.completeLattice.{u1} α))))) m₁ m₂)) (Sup.sup.{u2} (MeasurableSpace.{u2} β) (SemilatticeSup.toHasSup.{u2} (MeasurableSpace.{u2} β) (Lattice.toSemilatticeSup.{u2} (MeasurableSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (MeasurableSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.completeLattice.{u2} β))))) (MeasurableSpace.comap.{u2, u1} β α g m₁) (MeasurableSpace.comap.{u2, u1} β α g m₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m₁ : MeasurableSpace.{u1} α} {m₂ : MeasurableSpace.{u1} α} {g : β -> α}, Eq.{succ u2} (MeasurableSpace.{u2} β) (MeasurableSpace.comap.{u2, u1} β α g (Sup.sup.{u1} (MeasurableSpace.{u1} α) (SemilatticeSup.toSup.{u1} (MeasurableSpace.{u1} α) (Lattice.toSemilatticeSup.{u1} (MeasurableSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u1} α))))) m₁ m₂)) (Sup.sup.{u2} (MeasurableSpace.{u2} β) (SemilatticeSup.toSup.{u2} (MeasurableSpace.{u2} β) (Lattice.toSemilatticeSup.{u2} (MeasurableSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (MeasurableSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u2} β))))) (MeasurableSpace.comap.{u2, u1} β α g m₁) (MeasurableSpace.comap.{u2, u1} β α g m₂))
Case conversion may be inaccurate. Consider using '#align measurable_space.comap_sup MeasurableSpace.comap_supₓ'. -/
@[simp]
theorem comap_sup : (m₁ ⊔ m₂).comap g = m₁.comap g ⊔ m₂.comap g :=
  (gc_comap_map g).l_sup
#align measurable_space.comap_sup MeasurableSpace.comap_sup

/- warning: measurable_space.comap_supr -> MeasurableSpace.comap_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {g : β -> α} {m : ι -> (MeasurableSpace.{u1} α)}, Eq.{succ u2} (MeasurableSpace.{u2} β) (MeasurableSpace.comap.{u2, u1} β α g (iSup.{u1, u3} (MeasurableSpace.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.completeLattice.{u1} α))) ι (fun (i : ι) => m i))) (iSup.{u2, u3} (MeasurableSpace.{u2} β) (ConditionallyCompleteLattice.toHasSup.{u2} (MeasurableSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.completeLattice.{u2} β))) ι (fun (i : ι) => MeasurableSpace.comap.{u2, u1} β α g (m i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Sort.{u3}} {g : β -> α} {m : ι -> (MeasurableSpace.{u2} α)}, Eq.{succ u1} (MeasurableSpace.{u1} β) (MeasurableSpace.comap.{u1, u2} β α g (iSup.{u2, u3} (MeasurableSpace.{u2} α) (ConditionallyCompleteLattice.toSupSet.{u2} (MeasurableSpace.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u2} α))) ι (fun (i : ι) => m i))) (iSup.{u1, u3} (MeasurableSpace.{u1} β) (ConditionallyCompleteLattice.toSupSet.{u1} (MeasurableSpace.{u1} β) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasurableSpace.{u1} β) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u1} β))) ι (fun (i : ι) => MeasurableSpace.comap.{u1, u2} β α g (m i)))
Case conversion may be inaccurate. Consider using '#align measurable_space.comap_supr MeasurableSpace.comap_iSupₓ'. -/
@[simp]
theorem comap_iSup {m : ι → MeasurableSpace α} : (⨆ i, m i).comap g = ⨆ i, (m i).comap g :=
  (gc_comap_map g).l_iSup
#align measurable_space.comap_supr MeasurableSpace.comap_iSup

/- warning: measurable_space.map_top -> MeasurableSpace.map_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, Eq.{succ u2} (MeasurableSpace.{u2} β) (MeasurableSpace.map.{u1, u2} α β f (Top.top.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toHasTop.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.completeLattice.{u1} α)))) (Top.top.{u2} (MeasurableSpace.{u2} β) (CompleteLattice.toHasTop.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.completeLattice.{u2} β)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, Eq.{succ u2} (MeasurableSpace.{u2} β) (MeasurableSpace.map.{u1, u2} α β f (Top.top.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toTop.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u1} α)))) (Top.top.{u2} (MeasurableSpace.{u2} β) (CompleteLattice.toTop.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u2} β)))
Case conversion may be inaccurate. Consider using '#align measurable_space.map_top MeasurableSpace.map_topₓ'. -/
@[simp]
theorem map_top : (⊤ : MeasurableSpace α).map f = ⊤ :=
  (gc_comap_map f).u_top
#align measurable_space.map_top MeasurableSpace.map_top

/- warning: measurable_space.map_inf -> MeasurableSpace.map_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m₁ : MeasurableSpace.{u1} α} {m₂ : MeasurableSpace.{u1} α} {f : α -> β}, Eq.{succ u2} (MeasurableSpace.{u2} β) (MeasurableSpace.map.{u1, u2} α β f (Inf.inf.{u1} (MeasurableSpace.{u1} α) (SemilatticeInf.toHasInf.{u1} (MeasurableSpace.{u1} α) (Lattice.toSemilatticeInf.{u1} (MeasurableSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.completeLattice.{u1} α))))) m₁ m₂)) (Inf.inf.{u2} (MeasurableSpace.{u2} β) (SemilatticeInf.toHasInf.{u2} (MeasurableSpace.{u2} β) (Lattice.toSemilatticeInf.{u2} (MeasurableSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (MeasurableSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.completeLattice.{u2} β))))) (MeasurableSpace.map.{u1, u2} α β f m₁) (MeasurableSpace.map.{u1, u2} α β f m₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m₁ : MeasurableSpace.{u1} α} {m₂ : MeasurableSpace.{u1} α} {f : α -> β}, Eq.{succ u2} (MeasurableSpace.{u2} β) (MeasurableSpace.map.{u1, u2} α β f (Inf.inf.{u1} (MeasurableSpace.{u1} α) (Lattice.toInf.{u1} (MeasurableSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u1} α)))) m₁ m₂)) (Inf.inf.{u2} (MeasurableSpace.{u2} β) (Lattice.toInf.{u2} (MeasurableSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (MeasurableSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u2} β)))) (MeasurableSpace.map.{u1, u2} α β f m₁) (MeasurableSpace.map.{u1, u2} α β f m₂))
Case conversion may be inaccurate. Consider using '#align measurable_space.map_inf MeasurableSpace.map_infₓ'. -/
@[simp]
theorem map_inf : (m₁ ⊓ m₂).map f = m₁.map f ⊓ m₂.map f :=
  (gc_comap_map f).u_inf
#align measurable_space.map_inf MeasurableSpace.map_inf

/- warning: measurable_space.map_infi -> MeasurableSpace.map_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {f : α -> β} {m : ι -> (MeasurableSpace.{u1} α)}, Eq.{succ u2} (MeasurableSpace.{u2} β) (MeasurableSpace.map.{u1, u2} α β f (iInf.{u1, u3} (MeasurableSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.completeLattice.{u1} α))) ι (fun (i : ι) => m i))) (iInf.{u2, u3} (MeasurableSpace.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (MeasurableSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.completeLattice.{u2} β))) ι (fun (i : ι) => MeasurableSpace.map.{u1, u2} α β f (m i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Sort.{u3}} {f : α -> β} {m : ι -> (MeasurableSpace.{u2} α)}, Eq.{succ u1} (MeasurableSpace.{u1} β) (MeasurableSpace.map.{u2, u1} α β f (iInf.{u2, u3} (MeasurableSpace.{u2} α) (ConditionallyCompleteLattice.toInfSet.{u2} (MeasurableSpace.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u2} α))) ι (fun (i : ι) => m i))) (iInf.{u1, u3} (MeasurableSpace.{u1} β) (ConditionallyCompleteLattice.toInfSet.{u1} (MeasurableSpace.{u1} β) (CompleteLattice.toConditionallyCompleteLattice.{u1} (MeasurableSpace.{u1} β) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u1} β))) ι (fun (i : ι) => MeasurableSpace.map.{u2, u1} α β f (m i)))
Case conversion may be inaccurate. Consider using '#align measurable_space.map_infi MeasurableSpace.map_iInfₓ'. -/
@[simp]
theorem map_iInf {m : ι → MeasurableSpace α} : (⨅ i, m i).map f = ⨅ i, (m i).map f :=
  (gc_comap_map f).u_iInf
#align measurable_space.map_infi MeasurableSpace.map_iInf

/- warning: measurable_space.comap_map_le -> MeasurableSpace.comap_map_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {f : α -> β}, LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) (MeasurableSpace.comap.{u1, u2} α β f (MeasurableSpace.map.{u1, u2} α β f m)) m
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {f : α -> β}, LE.le.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instLEMeasurableSpace.{u2} α) (MeasurableSpace.comap.{u2, u1} α β f (MeasurableSpace.map.{u2, u1} α β f m)) m
Case conversion may be inaccurate. Consider using '#align measurable_space.comap_map_le MeasurableSpace.comap_map_leₓ'. -/
theorem comap_map_le : (m.map f).comap f ≤ m :=
  (gc_comap_map f).l_u_le _
#align measurable_space.comap_map_le MeasurableSpace.comap_map_le

/- warning: measurable_space.le_map_comap -> MeasurableSpace.le_map_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {g : β -> α}, LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) m (MeasurableSpace.map.{u2, u1} β α g (MeasurableSpace.comap.{u2, u1} β α g m))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {g : β -> α}, LE.le.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instLEMeasurableSpace.{u2} α) m (MeasurableSpace.map.{u1, u2} β α g (MeasurableSpace.comap.{u1, u2} β α g m))
Case conversion may be inaccurate. Consider using '#align measurable_space.le_map_comap MeasurableSpace.le_map_comapₓ'. -/
theorem le_map_comap : m ≤ (m.comap g).map g :=
  (gc_comap_map g).le_u_l _
#align measurable_space.le_map_comap MeasurableSpace.le_map_comap

end Functors

#print MeasurableSpace.comap_generateFrom /-
theorem comap_generateFrom {f : α → β} {s : Set (Set β)} :
    (generateFrom s).comap f = generateFrom (preimage f '' s) :=
  le_antisymm
    (comap_le_iff_le_map.2 <|
      generateFrom_le fun t hts => GenerateMeasurable.basic _ <| mem_image_of_mem _ <| hts)
    (generateFrom_le fun t ⟨u, hu, Eq⟩ => Eq ▸ ⟨u, GenerateMeasurable.basic _ hu, rfl⟩)
#align measurable_space.comap_generate_from MeasurableSpace.comap_generateFrom
-/

end MeasurableSpace

section MeasurableFunctions

open MeasurableSpace

/- warning: measurable_iff_le_map -> measurable_iff_le_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m₁ : MeasurableSpace.{u1} α} {m₂ : MeasurableSpace.{u2} β} {f : α -> β}, Iff (Measurable.{u1, u2} α β m₁ m₂ f) (LE.le.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.hasLe.{u2} β) m₂ (MeasurableSpace.map.{u1, u2} α β f m₁))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m₁ : MeasurableSpace.{u2} α} {m₂ : MeasurableSpace.{u1} β} {f : α -> β}, Iff (Measurable.{u2, u1} α β m₁ m₂ f) (LE.le.{u1} (MeasurableSpace.{u1} β) (MeasurableSpace.instLEMeasurableSpace.{u1} β) m₂ (MeasurableSpace.map.{u2, u1} α β f m₁))
Case conversion may be inaccurate. Consider using '#align measurable_iff_le_map measurable_iff_le_mapₓ'. -/
theorem measurable_iff_le_map {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} {f : α → β} :
    Measurable f ↔ m₂ ≤ m₁.map f :=
  Iff.rfl
#align measurable_iff_le_map measurable_iff_le_map

/- warning: measurable.le_map -> Measurable.le_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m₁ : MeasurableSpace.{u1} α} {m₂ : MeasurableSpace.{u2} β} {f : α -> β}, (Measurable.{u1, u2} α β m₁ m₂ f) -> (LE.le.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.hasLe.{u2} β) m₂ (MeasurableSpace.map.{u1, u2} α β f m₁))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m₁ : MeasurableSpace.{u2} α} {m₂ : MeasurableSpace.{u1} β} {f : α -> β}, (Measurable.{u2, u1} α β m₁ m₂ f) -> (LE.le.{u1} (MeasurableSpace.{u1} β) (MeasurableSpace.instLEMeasurableSpace.{u1} β) m₂ (MeasurableSpace.map.{u2, u1} α β f m₁))
Case conversion may be inaccurate. Consider using '#align measurable.le_map Measurable.le_mapₓ'. -/
/- warning: measurable.of_le_map -> Measurable.of_le_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m₁ : MeasurableSpace.{u1} α} {m₂ : MeasurableSpace.{u2} β} {f : α -> β}, (LE.le.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.hasLe.{u2} β) m₂ (MeasurableSpace.map.{u1, u2} α β f m₁)) -> (Measurable.{u1, u2} α β m₁ m₂ f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m₁ : MeasurableSpace.{u2} α} {m₂ : MeasurableSpace.{u1} β} {f : α -> β}, (LE.le.{u1} (MeasurableSpace.{u1} β) (MeasurableSpace.instLEMeasurableSpace.{u1} β) m₂ (MeasurableSpace.map.{u2, u1} α β f m₁)) -> (Measurable.{u2, u1} α β m₁ m₂ f)
Case conversion may be inaccurate. Consider using '#align measurable.of_le_map Measurable.of_le_mapₓ'. -/
alias measurable_iff_le_map ↔ Measurable.le_map Measurable.of_le_map
#align measurable.le_map Measurable.le_map
#align measurable.of_le_map Measurable.of_le_map

/- warning: measurable_iff_comap_le -> measurable_iff_comap_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m₁ : MeasurableSpace.{u1} α} {m₂ : MeasurableSpace.{u2} β} {f : α -> β}, Iff (Measurable.{u1, u2} α β m₁ m₂ f) (LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) (MeasurableSpace.comap.{u1, u2} α β f m₂) m₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m₁ : MeasurableSpace.{u2} α} {m₂ : MeasurableSpace.{u1} β} {f : α -> β}, Iff (Measurable.{u2, u1} α β m₁ m₂ f) (LE.le.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instLEMeasurableSpace.{u2} α) (MeasurableSpace.comap.{u2, u1} α β f m₂) m₁)
Case conversion may be inaccurate. Consider using '#align measurable_iff_comap_le measurable_iff_comap_leₓ'. -/
theorem measurable_iff_comap_le {m₁ : MeasurableSpace α} {m₂ : MeasurableSpace β} {f : α → β} :
    Measurable f ↔ m₂.comap f ≤ m₁ :=
  comap_le_iff_le_map.symm
#align measurable_iff_comap_le measurable_iff_comap_le

/- warning: measurable.comap_le -> Measurable.comap_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m₁ : MeasurableSpace.{u1} α} {m₂ : MeasurableSpace.{u2} β} {f : α -> β}, (Measurable.{u1, u2} α β m₁ m₂ f) -> (LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) (MeasurableSpace.comap.{u1, u2} α β f m₂) m₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m₁ : MeasurableSpace.{u2} α} {m₂ : MeasurableSpace.{u1} β} {f : α -> β}, (Measurable.{u2, u1} α β m₁ m₂ f) -> (LE.le.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instLEMeasurableSpace.{u2} α) (MeasurableSpace.comap.{u2, u1} α β f m₂) m₁)
Case conversion may be inaccurate. Consider using '#align measurable.comap_le Measurable.comap_leₓ'. -/
/- warning: measurable.of_comap_le -> Measurable.of_comap_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m₁ : MeasurableSpace.{u1} α} {m₂ : MeasurableSpace.{u2} β} {f : α -> β}, (LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) (MeasurableSpace.comap.{u1, u2} α β f m₂) m₁) -> (Measurable.{u1, u2} α β m₁ m₂ f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m₁ : MeasurableSpace.{u2} α} {m₂ : MeasurableSpace.{u1} β} {f : α -> β}, (LE.le.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instLEMeasurableSpace.{u2} α) (MeasurableSpace.comap.{u2, u1} α β f m₂) m₁) -> (Measurable.{u2, u1} α β m₁ m₂ f)
Case conversion may be inaccurate. Consider using '#align measurable.of_comap_le Measurable.of_comap_leₓ'. -/
alias measurable_iff_comap_le ↔ Measurable.comap_le Measurable.of_comap_le
#align measurable.comap_le Measurable.comap_le
#align measurable.of_comap_le Measurable.of_comap_le

#print comap_measurable /-
theorem comap_measurable {m : MeasurableSpace β} (f : α → β) : measurable[m.comap f] f :=
  fun s hs => ⟨s, hs, rfl⟩
#align comap_measurable comap_measurable
-/

/- warning: measurable.mono -> Measurable.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ma : MeasurableSpace.{u1} α} {ma' : MeasurableSpace.{u1} α} {mb : MeasurableSpace.{u2} β} {mb' : MeasurableSpace.{u2} β} {f : α -> β}, (Measurable.{u1, u2} α β ma mb f) -> (LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) ma ma') -> (LE.le.{u2} (MeasurableSpace.{u2} β) (MeasurableSpace.hasLe.{u2} β) mb' mb) -> (Measurable.{u1, u2} α β ma' mb' f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ma : MeasurableSpace.{u2} α} {ma' : MeasurableSpace.{u2} α} {mb : MeasurableSpace.{u1} β} {mb' : MeasurableSpace.{u1} β} {f : α -> β}, (Measurable.{u2, u1} α β ma mb f) -> (LE.le.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instLEMeasurableSpace.{u2} α) ma ma') -> (LE.le.{u1} (MeasurableSpace.{u1} β) (MeasurableSpace.instLEMeasurableSpace.{u1} β) mb' mb) -> (Measurable.{u2, u1} α β ma' mb' f)
Case conversion may be inaccurate. Consider using '#align measurable.mono Measurable.monoₓ'. -/
theorem Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : MeasurableSpace β} {f : α → β}
    (hf : @Measurable α β ma mb f) (ha : ma ≤ ma') (hb : mb' ≤ mb) : @Measurable α β ma' mb' f :=
  fun t ht => ha _ <| hf <| hb _ ht
#align measurable.mono Measurable.mono

/- warning: measurable_from_top -> measurable_from_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β}, Measurable.{u1, u2} α β (Top.top.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toHasTop.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.completeLattice.{u1} α))) _inst_1 f
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β}, Measurable.{u1, u2} α β (Top.top.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toTop.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u1} α))) _inst_1 f
Case conversion may be inaccurate. Consider using '#align measurable_from_top measurable_from_topₓ'. -/
@[measurability]
theorem measurable_from_top [MeasurableSpace β] {f : α → β} : measurable[⊤] f := fun s hs => trivial
#align measurable_from_top measurable_from_top

/- warning: measurable_generate_from -> measurable_generateFrom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {s : Set.{u2} (Set.{u2} β)} {f : α -> β}, (forall (t : Set.{u2} β), (Membership.Mem.{u2, u2} (Set.{u2} β) (Set.{u2} (Set.{u2} β)) (Set.hasMem.{u2} (Set.{u2} β)) t s) -> (MeasurableSet.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f t))) -> (Measurable.{u1, u2} α β _inst_1 (MeasurableSpace.generateFrom.{u2} β s) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {s : Set.{u1} (Set.{u1} β)} {f : α -> β}, (forall (t : Set.{u1} β), (Membership.mem.{u1, u1} (Set.{u1} β) (Set.{u1} (Set.{u1} β)) (Set.instMembershipSet.{u1} (Set.{u1} β)) t s) -> (MeasurableSet.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f t))) -> (Measurable.{u2, u1} α β _inst_1 (MeasurableSpace.generateFrom.{u1} β s) f)
Case conversion may be inaccurate. Consider using '#align measurable_generate_from measurable_generateFromₓ'. -/
theorem measurable_generateFrom [MeasurableSpace α] {s : Set (Set β)} {f : α → β}
    (h : ∀ t ∈ s, MeasurableSet (f ⁻¹' t)) : @Measurable _ _ _ (generateFrom s) f :=
  Measurable.of_le_map <| generateFrom_le h
#align measurable_generate_from measurable_generateFrom

variable {f g : α → β}

section TypeclassMeasurableSpace

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/- warning: subsingleton.measurable -> Subsingleton.measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] [_inst_4 : Subsingleton.{succ u1} α], Measurable.{u1, u2} α β _inst_1 _inst_2 f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] [_inst_4 : Subsingleton.{succ u2} α], Measurable.{u2, u1} α β _inst_1 _inst_2 f
Case conversion may be inaccurate. Consider using '#align subsingleton.measurable Subsingleton.measurableₓ'. -/
@[nontriviality, measurability]
theorem Subsingleton.measurable [Subsingleton α] : Measurable f := fun s hs =>
  @Subsingleton.measurableSet α _ _ _
#align subsingleton.measurable Subsingleton.measurable

#print measurable_of_subsingleton_codomain /-
@[nontriviality, measurability]
theorem measurable_of_subsingleton_codomain [Subsingleton β] (f : α → β) : Measurable f :=
  fun s hs => Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s
#align measurable_of_subsingleton_codomain measurable_of_subsingleton_codomain
-/

/- warning: measurable_one -> measurable_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] [_inst_4 : One.{u1} α], Measurable.{u2, u1} β α _inst_2 _inst_1 (OfNat.ofNat.{max u2 u1} (β -> α) 1 (OfNat.mk.{max u2 u1} (β -> α) 1 (One.one.{max u2 u1} (β -> α) (Pi.instOne.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => _inst_4)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] [_inst_4 : One.{u2} α], Measurable.{u1, u2} β α _inst_2 _inst_1 (OfNat.ofNat.{max u2 u1} (β -> α) 1 (One.toOfNat1.{max u2 u1} (β -> α) (Pi.instOne.{u1, u2} β (fun (a._@.Mathlib.MeasureTheory.MeasurableSpace._hyg.2074 : β) => α) (fun (i : β) => _inst_4))))
Case conversion may be inaccurate. Consider using '#align measurable_one measurable_oneₓ'. -/
@[to_additive]
theorem measurable_one [One α] : Measurable (1 : β → α) :=
  @measurable_const _ _ _ _ 1
#align measurable_one measurable_one
#align measurable_zero measurable_zero

/- warning: measurable_of_empty -> measurable_of_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] [_inst_4 : IsEmpty.{succ u1} α] (f : α -> β), Measurable.{u1, u2} α β _inst_1 _inst_2 f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] [_inst_4 : IsEmpty.{succ u2} α] (f : α -> β), Measurable.{u2, u1} α β _inst_1 _inst_2 f
Case conversion may be inaccurate. Consider using '#align measurable_of_empty measurable_of_emptyₓ'. -/
theorem measurable_of_empty [IsEmpty α] (f : α → β) : Measurable f :=
  Subsingleton.measurable
#align measurable_of_empty measurable_of_empty

#print measurable_of_empty_codomain /-
theorem measurable_of_empty_codomain [IsEmpty β] (f : α → β) : Measurable f :=
  haveI := Function.isEmpty f
  measurable_of_empty f
#align measurable_of_empty_codomain measurable_of_empty_codomain
-/

/- warning: measurable_const' -> measurable_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {f : β -> α}, (forall (x : β) (y : β), Eq.{succ u1} α (f x) (f y)) -> (Measurable.{u2, u1} β α _inst_2 _inst_1 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {f : β -> α}, (forall (x : β) (y : β), Eq.{succ u2} α (f x) (f y)) -> (Measurable.{u1, u2} β α _inst_2 _inst_1 f)
Case conversion may be inaccurate. Consider using '#align measurable_const' measurable_const'ₓ'. -/
/-- A version of `measurable_const` that assumes `f x = f y` for all `x, y`. This version works
for functions between empty types. -/
theorem measurable_const' {f : β → α} (hf : ∀ x y, f x = f y) : Measurable f :=
  by
  cases isEmpty_or_nonempty β
  · exact measurable_of_empty f
  · convert measurable_const
    exact funext fun x => hf x h.some
#align measurable_const' measurable_const'

/- warning: measurable_nat_cast -> measurable_natCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] [_inst_4 : NatCast.{u1} α] (n : Nat), Measurable.{u2, u1} β α _inst_2 _inst_1 ((fun (a : Type) (b : Sort.{max (succ u2) (succ u1)}) [self : HasLiftT.{1, max (succ u2) (succ u1)} a b] => self.0) Nat (β -> α) (HasLiftT.mk.{1, max (succ u2) (succ u1)} Nat (β -> α) (CoeTCₓ.coe.{1, max (succ u2) (succ u1)} Nat (β -> α) (Nat.castCoe.{max u2 u1} (β -> α) (Pi.hasNatCast.{u2, u1} β (fun (ᾰ : β) => α) (fun (a : β) => _inst_4))))) n)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] [_inst_4 : NatCast.{u2} α] (n : Nat), Measurable.{u1, u2} β α _inst_2 _inst_1 (Nat.cast.{max u2 u1} (β -> α) (Pi.natCast.{u1, u2} β (fun (a._@.Mathlib.MeasureTheory.MeasurableSpace._hyg.2320 : β) => α) (fun (a : β) => _inst_4)) n)
Case conversion may be inaccurate. Consider using '#align measurable_nat_cast measurable_natCastₓ'. -/
@[measurability]
theorem measurable_natCast [NatCast α] (n : ℕ) : Measurable (n : β → α) :=
  @measurable_const α _ _ _ n
#align measurable_nat_cast measurable_natCast

/- warning: measurable_int_cast -> measurable_intCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] [_inst_4 : IntCast.{u1} α] (n : Int), Measurable.{u2, u1} β α _inst_2 _inst_1 ((fun (a : Type) (b : Sort.{max (succ u2) (succ u1)}) [self : HasLiftT.{1, max (succ u2) (succ u1)} a b] => self.0) Int (β -> α) (HasLiftT.mk.{1, max (succ u2) (succ u1)} Int (β -> α) (CoeTCₓ.coe.{1, max (succ u2) (succ u1)} Int (β -> α) (Int.castCoe.{max u2 u1} (β -> α) (Pi.hasIntCast.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => _inst_4))))) n)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] [_inst_4 : IntCast.{u2} α] (n : Int), Measurable.{u1, u2} β α _inst_2 _inst_1 (Int.cast.{max u2 u1} (β -> α) (Pi.intCast.{u1, u2} β (fun (a._@.Mathlib.MeasureTheory.MeasurableSpace._hyg.2370 : β) => α) (fun (i : β) => _inst_4)) n)
Case conversion may be inaccurate. Consider using '#align measurable_int_cast measurable_intCastₓ'. -/
@[measurability]
theorem measurable_intCast [IntCast α] (n : ℤ) : Measurable (n : β → α) :=
  @measurable_const α _ _ _ n
#align measurable_int_cast measurable_intCast

/- warning: measurable_of_finite -> measurable_of_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] [_inst_4 : Finite.{succ u1} α] [_inst_5 : MeasurableSingletonClass.{u1} α _inst_1] (f : α -> β), Measurable.{u1, u2} α β _inst_1 _inst_2 f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] [_inst_4 : Finite.{succ u2} α] [_inst_5 : MeasurableSingletonClass.{u2} α _inst_1] (f : α -> β), Measurable.{u2, u1} α β _inst_1 _inst_2 f
Case conversion may be inaccurate. Consider using '#align measurable_of_finite measurable_of_finiteₓ'. -/
theorem measurable_of_finite [Finite α] [MeasurableSingletonClass α] (f : α → β) : Measurable f :=
  fun s hs => (f ⁻¹' s).toFinite.MeasurableSet
#align measurable_of_finite measurable_of_finite

/- warning: measurable_of_countable -> measurable_of_countable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] [_inst_4 : Countable.{succ u1} α] [_inst_5 : MeasurableSingletonClass.{u1} α _inst_1] (f : α -> β), Measurable.{u1, u2} α β _inst_1 _inst_2 f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] [_inst_4 : Countable.{succ u2} α] [_inst_5 : MeasurableSingletonClass.{u2} α _inst_1] (f : α -> β), Measurable.{u2, u1} α β _inst_1 _inst_2 f
Case conversion may be inaccurate. Consider using '#align measurable_of_countable measurable_of_countableₓ'. -/
theorem measurable_of_countable [Countable α] [MeasurableSingletonClass α] (f : α → β) :
    Measurable f := fun s hs => (f ⁻¹' s).to_countable.MeasurableSet
#align measurable_of_countable measurable_of_countable

end TypeclassMeasurableSpace

variable {m : MeasurableSpace α}

include m

#print Measurable.iterate /-
@[measurability]
theorem Measurable.iterate {f : α → α} (hf : Measurable f) : ∀ n, Measurable (f^[n])
  | 0 => measurable_id
  | n + 1 => (Measurable.iterate n).comp hf
#align measurable.iterate Measurable.iterate
-/

variable {mβ : MeasurableSpace β}

include mβ

#print measurableSet_preimage /-
@[measurability]
theorem measurableSet_preimage {t : Set β} (hf : Measurable f) (ht : MeasurableSet t) :
    MeasurableSet (f ⁻¹' t) :=
  hf ht
#align measurable_set_preimage measurableSet_preimage
-/

/- warning: measurable.piecewise -> Measurable.piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {f : α -> β} {g : α -> β} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {_x : DecidablePred.{succ u1} α (fun (_x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) _x s)}, (MeasurableSet.{u1} α m s) -> (Measurable.{u1, u2} α β m mβ f) -> (Measurable.{u1, u2} α β m mβ g) -> (Measurable.{u1, u2} α β m mβ (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _x j)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {f : α -> β} {g : α -> β} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} {_x : DecidablePred.{succ u2} α (fun (_x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) _x s)}, (MeasurableSet.{u2} α m s) -> (Measurable.{u2, u1} α β m mβ f) -> (Measurable.{u2, u1} α β m mβ g) -> (Measurable.{u2, u1} α β m mβ (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _x j)))
Case conversion may be inaccurate. Consider using '#align measurable.piecewise Measurable.piecewiseₓ'. -/
@[measurability]
theorem Measurable.piecewise {_ : DecidablePred (· ∈ s)} (hs : MeasurableSet s) (hf : Measurable f)
    (hg : Measurable g) : Measurable (piecewise s f g) :=
  by
  intro t ht
  rw [piecewise_preimage]
  exact hs.ite (hf ht) (hg ht)
#align measurable.piecewise Measurable.piecewise

/- warning: measurable.ite -> Measurable.ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : α -> β} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {p : α -> Prop} {_x : DecidablePred.{succ u1} α p}, (MeasurableSet.{u1} α m (setOf.{u1} α (fun (a : α) => p a))) -> (Measurable.{u1, u2} α β m mβ f) -> (Measurable.{u1, u2} α β m mβ g) -> (Measurable.{u1, u2} α β m mβ (fun (x : α) => ite.{succ u2} β (p x) (_x x) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : α -> β} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} {p : α -> Prop} {_x : DecidablePred.{succ u2} α p}, (MeasurableSet.{u2} α m (setOf.{u2} α (fun (a : α) => p a))) -> (Measurable.{u2, u1} α β m mβ f) -> (Measurable.{u2, u1} α β m mβ g) -> (Measurable.{u2, u1} α β m mβ (fun (x : α) => ite.{succ u1} β (p x) (_x x) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align measurable.ite Measurable.iteₓ'. -/
/-- this is slightly different from `measurable.piecewise`. It can be used to show
`measurable (ite (x=0) 0 1)` by
`exact measurable.ite (measurable_set_singleton 0) measurable_const measurable_const`,
but replacing `measurable.ite` by `measurable.piecewise` in that example proof does not work. -/
theorem Measurable.ite {p : α → Prop} {_ : DecidablePred p} (hp : MeasurableSet { a : α | p a })
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => ite (p x) (f x) (g x) :=
  Measurable.piecewise hp hf hg
#align measurable.ite Measurable.ite

#print Measurable.indicator /-
@[measurability]
theorem Measurable.indicator [Zero β] (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable (s.indicator f) :=
  hf.piecewise hs measurable_const
#align measurable.indicator Measurable.indicator
-/

#print measurableSet_mulSupport /-
@[measurability, to_additive]
theorem measurableSet_mulSupport [One β] [MeasurableSingletonClass β] (hf : Measurable f) :
    MeasurableSet (mulSupport f) :=
  hf (measurableSet_singleton 1).compl
#align measurable_set_mul_support measurableSet_mulSupport
#align measurable_set_support measurableSet_support
-/

/- warning: measurable.measurable_of_countable_ne -> Measurable.measurable_of_countable_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : α -> β} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} [_inst_1 : MeasurableSingletonClass.{u1} α m], (Measurable.{u1, u2} α β m mβ f) -> (Set.Countable.{u1} α (setOf.{u1} α (fun (x : α) => Ne.{succ u2} β (f x) (g x)))) -> (Measurable.{u1, u2} α β m mβ g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : α -> β} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} [_inst_1 : MeasurableSingletonClass.{u2} α m], (Measurable.{u2, u1} α β m mβ f) -> (Set.Countable.{u2} α (setOf.{u2} α (fun (x : α) => Ne.{succ u1} β (f x) (g x)))) -> (Measurable.{u2, u1} α β m mβ g)
Case conversion may be inaccurate. Consider using '#align measurable.measurable_of_countable_ne Measurable.measurable_of_countable_neₓ'. -/
/-- If a function coincides with a measurable function outside of a countable set, it is
measurable. -/
theorem Measurable.measurable_of_countable_ne [MeasurableSingletonClass α] (hf : Measurable f)
    (h : Set.Countable { x | f x ≠ g x }) : Measurable g :=
  by
  intro t ht
  have : g ⁻¹' t = g ⁻¹' t ∩ { x | f x = g x }ᶜ ∪ g ⁻¹' t ∩ { x | f x = g x } := by
    simp [← inter_union_distrib_left]
  rw [this]
  apply MeasurableSet.union (h.mono (inter_subset_right _ _)).MeasurableSet
  have : g ⁻¹' t ∩ { x : α | f x = g x } = f ⁻¹' t ∩ { x : α | f x = g x } :=
    by
    ext x
    simp (config := { contextual := true })
  rw [this]
  exact (hf ht).inter h.measurable_set.of_compl
#align measurable.measurable_of_countable_ne Measurable.measurable_of_countable_ne

end MeasurableFunctions

section Constructions

instance : MeasurableSpace Empty :=
  ⊤

instance : MeasurableSpace PUnit :=
  ⊤

-- this also works for `unit`
instance : MeasurableSpace Bool :=
  ⊤

instance : MeasurableSpace ℕ :=
  ⊤

instance : MeasurableSpace ℤ :=
  ⊤

instance : MeasurableSpace ℚ :=
  ⊤

instance : MeasurableSingletonClass Empty :=
  ⟨fun _ => trivial⟩

instance : MeasurableSingletonClass PUnit :=
  ⟨fun _ => trivial⟩

instance : MeasurableSingletonClass Bool :=
  ⟨fun _ => trivial⟩

instance : MeasurableSingletonClass ℕ :=
  ⟨fun _ => trivial⟩

instance : MeasurableSingletonClass ℤ :=
  ⟨fun _ => trivial⟩

instance : MeasurableSingletonClass ℚ :=
  ⟨fun _ => trivial⟩

/- warning: measurable_to_countable -> measurable_to_countable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Countable.{succ u1} α] [_inst_3 : MeasurableSpace.{u2} β] {f : β -> α}, (forall (y : β), MeasurableSet.{u2} β _inst_3 (Set.preimage.{u2, u1} β α f (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (f y)))) -> (Measurable.{u2, u1} β α _inst_3 _inst_1 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : Countable.{succ u2} α] [_inst_3 : MeasurableSpace.{u1} β] {f : β -> α}, (forall (y : β), MeasurableSet.{u1} β _inst_3 (Set.preimage.{u1, u2} β α f (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) (f y)))) -> (Measurable.{u1, u2} β α _inst_3 _inst_1 f)
Case conversion may be inaccurate. Consider using '#align measurable_to_countable measurable_to_countableₓ'. -/
theorem measurable_to_countable [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β → α}
    (h : ∀ y, MeasurableSet (f ⁻¹' {f y})) : Measurable f :=
  by
  intro s hs
  rw [← bUnion_preimage_singleton]
  refine' MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun hy => _
  by_cases hyf : y ∈ range f
  · rcases hyf with ⟨y, rfl⟩
    apply h
  · simp only [preimage_singleton_eq_empty.2 hyf, MeasurableSet.empty]
#align measurable_to_countable measurable_to_countable

/- warning: measurable_to_countable' -> measurable_to_countable' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Countable.{succ u1} α] [_inst_3 : MeasurableSpace.{u2} β] {f : β -> α}, (forall (x : α), MeasurableSet.{u2} β _inst_3 (Set.preimage.{u2, u1} β α f (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))) -> (Measurable.{u2, u1} β α _inst_3 _inst_1 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : Countable.{succ u2} α] [_inst_3 : MeasurableSpace.{u1} β] {f : β -> α}, (forall (x : α), MeasurableSet.{u1} β _inst_3 (Set.preimage.{u1, u2} β α f (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) x))) -> (Measurable.{u1, u2} β α _inst_3 _inst_1 f)
Case conversion may be inaccurate. Consider using '#align measurable_to_countable' measurable_to_countable'ₓ'. -/
theorem measurable_to_countable' [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β → α}
    (h : ∀ x, MeasurableSet (f ⁻¹' {x})) : Measurable f :=
  measurable_to_countable fun y => h (f y)
#align measurable_to_countable' measurable_to_countable'

#print measurable_unit /-
@[measurability]
theorem measurable_unit [MeasurableSpace α] (f : Unit → α) : Measurable f :=
  measurable_from_top
#align measurable_unit measurable_unit
-/

section Nat

variable [MeasurableSpace α]

#print measurable_from_nat /-
@[measurability]
theorem measurable_from_nat {f : ℕ → α} : Measurable f :=
  measurable_from_top
#align measurable_from_nat measurable_from_nat
-/

#print measurable_to_nat /-
theorem measurable_to_nat {f : α → ℕ} : (∀ y, MeasurableSet (f ⁻¹' {f y})) → Measurable f :=
  measurable_to_countable
#align measurable_to_nat measurable_to_nat
-/

#print measurable_to_bool /-
theorem measurable_to_bool {f : α → Bool} (h : MeasurableSet (f ⁻¹' {true})) : Measurable f :=
  by
  apply measurable_to_countable'
  rintro (- | -)
  · convert h.compl
    rw [← preimage_compl, Bool.compl_singleton, Bool.not_true]
  exact h
#align measurable_to_bool measurable_to_bool
-/

#print measurable_findGreatest' /-
theorem measurable_findGreatest' {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] {N : ℕ}
    (hN : ∀ k ≤ N, MeasurableSet { x | Nat.findGreatest (p x) N = k }) :
    Measurable fun x => Nat.findGreatest (p x) N :=
  measurable_to_nat fun x => hN _ N.findGreatest_le
#align measurable_find_greatest' measurable_findGreatest'
-/

#print measurable_findGreatest /-
theorem measurable_findGreatest {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] {N}
    (hN : ∀ k ≤ N, MeasurableSet { x | p x k }) : Measurable fun x => Nat.findGreatest (p x) N :=
  by
  refine' measurable_findGreatest' fun k hk => _
  simp only [Nat.findGreatest_eq_iff, set_of_and, set_of_forall, ← compl_set_of]
  repeat'
    apply_rules [MeasurableSet.inter, MeasurableSet.const, MeasurableSet.iInter,
        MeasurableSet.compl, hN] <;>
      try intros
#align measurable_find_greatest measurable_findGreatest
-/

#print measurable_find /-
theorem measurable_find {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] (hp : ∀ x, ∃ N, p x N)
    (hm : ∀ k, MeasurableSet { x | p x k }) : Measurable fun x => Nat.find (hp x) :=
  by
  refine' measurable_to_nat fun x => _
  rw [preimage_find_eq_disjointed]
  exact MeasurableSet.disjointed hm _
#align measurable_find measurable_find
-/

end Nat

section Quotient

variable [MeasurableSpace α] [MeasurableSpace β]

instance {α} {r : α → α → Prop} [m : MeasurableSpace α] : MeasurableSpace (Quot r) :=
  m.map (Quot.mk r)

instance {α} {s : Setoid α} [m : MeasurableSpace α] : MeasurableSpace (Quotient s) :=
  m.map Quotient.mk''

#print QuotientGroup.measurableSpace /-
@[to_additive]
instance QuotientGroup.measurableSpace {G} [Group G] [MeasurableSpace G] (S : Subgroup G) :
    MeasurableSpace (G ⧸ S) :=
  Quotient.instMeasurableSpace
#align quotient_group.measurable_space QuotientGroup.measurableSpace
#align quotient_add_group.measurable_space QuotientAddGroup.measurableSpace
-/

#print measurableSet_quotient /-
theorem measurableSet_quotient {s : Setoid α} {t : Set (Quotient s)} :
    MeasurableSet t ↔ MeasurableSet (Quotient.mk'' ⁻¹' t) :=
  Iff.rfl
#align measurable_set_quotient measurableSet_quotient
-/

/- warning: measurable_from_quotient -> measurable_from_quotient is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {s : Setoid.{succ u1} α} {f : (Quotient.{succ u1} α s) -> β}, Iff (Measurable.{u1, u2} (Quotient.{succ u1} α s) β (Quotient.instMeasurableSpace.{u1} α s _inst_1) _inst_2 f) (Measurable.{u1, u2} α β _inst_1 _inst_2 (Function.comp.{succ u1, succ u1, succ u2} α (Quotient.{succ u1} α s) β f (Quotient.mk''.{succ u1} α s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {s : Setoid.{succ u2} α} {f : (Quotient.{succ u2} α s) -> β}, Iff (Measurable.{u2, u1} (Quotient.{succ u2} α s) β (Quotient.instMeasurableSpace.{u2} α s _inst_1) _inst_2 f) (Measurable.{u2, u1} α β _inst_1 _inst_2 (Function.comp.{succ u2, succ u2, succ u1} α (Quotient.{succ u2} α s) β f (Quotient.mk''.{succ u2} α s)))
Case conversion may be inaccurate. Consider using '#align measurable_from_quotient measurable_from_quotientₓ'. -/
theorem measurable_from_quotient {s : Setoid α} {f : Quotient s → β} :
    Measurable f ↔ Measurable (f ∘ Quotient.mk'') :=
  Iff.rfl
#align measurable_from_quotient measurable_from_quotient

#print measurable_quotient_mk' /-
@[measurability]
theorem measurable_quotient_mk' [s : Setoid α] : Measurable (Quotient.mk' : α → Quotient s) :=
  fun s => id
#align measurable_quotient_mk measurable_quotient_mk'
-/

#print measurable_quotient_mk'' /-
@[measurability]
theorem measurable_quotient_mk'' {s : Setoid α} : Measurable (Quotient.mk'' : α → Quotient s) :=
  fun s => id
#align measurable_quotient_mk' measurable_quotient_mk''
-/

#print measurable_quot_mk /-
@[measurability]
theorem measurable_quot_mk {r : α → α → Prop} : Measurable (Quot.mk r) := fun s => id
#align measurable_quot_mk measurable_quot_mk
-/

#print QuotientGroup.measurable_coe /-
@[to_additive]
theorem QuotientGroup.measurable_coe {G} [Group G] [MeasurableSpace G] {S : Subgroup G} :
    Measurable (coe : G → G ⧸ S) :=
  measurable_quotient_mk''
#align quotient_group.measurable_coe QuotientGroup.measurable_coe
#align quotient_add_group.measurable_coe QuotientAddGroup.measurable_coe
-/

attribute [measurability] QuotientGroup.measurable_coe QuotientAddGroup.measurable_coe

#print QuotientGroup.measurable_from_quotient /-
@[to_additive]
theorem QuotientGroup.measurable_from_quotient {G} [Group G] [MeasurableSpace G] {S : Subgroup G}
    {f : G ⧸ S → α} : Measurable f ↔ Measurable (f ∘ (coe : G → G ⧸ S)) :=
  measurable_from_quotient
#align quotient_group.measurable_from_quotient QuotientGroup.measurable_from_quotient
#align quotient_add_group.measurable_from_quotient QuotientAddGroup.measurable_from_quotient
-/

end Quotient

section Subtype

instance {α} {p : α → Prop} [m : MeasurableSpace α] : MeasurableSpace (Subtype p) :=
  m.comap (coe : _ → α)

section

variable [MeasurableSpace α]

#print measurable_subtype_coe /-
@[measurability]
theorem measurable_subtype_coe {p : α → Prop} : Measurable (coe : Subtype p → α) :=
  MeasurableSpace.le_map_comap
#align measurable_subtype_coe measurable_subtype_coe
-/

instance {p : α → Prop} [MeasurableSingletonClass α] : MeasurableSingletonClass (Subtype p)
    where measurableSet_singleton x :=
    by
    have : MeasurableSet {(x : α)} := measurable_set_singleton _
    convert@measurable_subtype_coe α _ p _ this
    ext y
    simp [Subtype.ext_iff]

end

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β}

include m

#print MeasurableSet.subtype_image /-
theorem MeasurableSet.subtype_image {s : Set α} {t : Set s} (hs : MeasurableSet s) :
    MeasurableSet t → MeasurableSet ((coe : s → α) '' t)
  | ⟨u, (hu : MeasurableSet u), (Eq : coe ⁻¹' u = t)⟩ =>
    by
    rw [← Eq, Subtype.image_preimage_coe]
    exact hu.inter hs
#align measurable_set.subtype_image MeasurableSet.subtype_image
-/

include mβ

#print Measurable.subtype_coe /-
@[measurability]
theorem Measurable.subtype_coe {p : β → Prop} {f : α → Subtype p} (hf : Measurable f) :
    Measurable fun a : α => (f a : β) :=
  measurable_subtype_coe.comp hf
#align measurable.subtype_coe Measurable.subtype_coe
-/

/- warning: measurable.subtype_mk -> Measurable.subtype_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {p : β -> Prop} {f : α -> β}, (Measurable.{u1, u2} α β m mβ f) -> (forall {h : forall (x : α), p (f x)}, Measurable.{u1, u2} α (Subtype.{succ u2} β p) m (Subtype.instMeasurableSpace.{u2} β p mβ) (fun (x : α) => Subtype.mk.{succ u2} β p (f x) (h x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} {p : β -> Prop} {f : α -> β}, (Measurable.{u2, u1} α β m mβ f) -> (forall {h : forall (x : α), p (f x)}, Measurable.{u2, u1} α (Subtype.{succ u1} β p) m (Subtype.instMeasurableSpace.{u1} β p mβ) (fun (x : α) => Subtype.mk.{succ u1} β p (f x) (h x)))
Case conversion may be inaccurate. Consider using '#align measurable.subtype_mk Measurable.subtype_mkₓ'. -/
@[measurability]
theorem Measurable.subtype_mk {p : β → Prop} {f : α → β} (hf : Measurable f) {h : ∀ x, p (f x)} :
    Measurable fun x => (⟨f x, h x⟩ : Subtype p) := fun t ⟨s, hs⟩ =>
  hs.2 ▸ by simp only [← preimage_comp, (· ∘ ·), Subtype.coe_mk, hf hs.1]
#align measurable.subtype_mk Measurable.subtype_mk

/- warning: measurable_of_measurable_union_cover -> measurable_of_measurable_union_cover is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {f : α -> β} (s : Set.{u1} α) (t : Set.{u1} α), (MeasurableSet.{u1} α m s) -> (MeasurableSet.{u1} α m t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.univ.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) -> (Measurable.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) m) mβ (fun (a : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) a))) -> (Measurable.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) β (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) m) mβ (fun (a : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t))))) a))) -> (Measurable.{u1, u2} α β m mβ f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} {f : α -> β} (s : Set.{u2} α) (t : Set.{u2} α), (MeasurableSet.{u2} α m s) -> (MeasurableSet.{u2} α m t) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.univ.{u2} α) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) -> (Measurable.{u2, u1} (Set.Elem.{u2} α s) β (Subtype.instMeasurableSpace.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) m) mβ (fun (a : Set.Elem.{u2} α s) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) a))) -> (Measurable.{u2, u1} (Set.Elem.{u2} α t) β (Subtype.instMeasurableSpace.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) m) mβ (fun (a : Set.Elem.{u2} α t) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) a))) -> (Measurable.{u2, u1} α β m mβ f)
Case conversion may be inaccurate. Consider using '#align measurable_of_measurable_union_cover measurable_of_measurable_union_coverₓ'. -/
theorem measurable_of_measurable_union_cover {f : α → β} (s t : Set α) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : univ ⊆ s ∪ t) (hc : Measurable fun a : s => f a)
    (hd : Measurable fun a : t => f a) : Measurable f :=
  by
  intro u hu
  convert(hs.subtype_image (hc hu)).union (ht.subtype_image (hd hu))
  change f ⁻¹' u = coe '' (coe ⁻¹' (f ⁻¹' u) : Set s) ∪ coe '' (coe ⁻¹' (f ⁻¹' u) : Set t)
  rw [image_preimage_eq_inter_range, image_preimage_eq_inter_range, Subtype.range_coe,
    Subtype.range_coe, ← inter_distrib_left, univ_subset_iff.1 h, inter_univ]
#align measurable_of_measurable_union_cover measurable_of_measurable_union_cover

/- warning: measurable_of_restrict_of_restrict_compl -> measurable_of_restrict_of_restrict_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {f : α -> β} {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (Measurable.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) m) mβ (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f)) -> (Measurable.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) β (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) m) mβ (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) f)) -> (Measurable.{u1, u2} α β m mβ f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} {f : α -> β} {s : Set.{u2} α}, (MeasurableSet.{u2} α m s) -> (Measurable.{u2, u1} (Set.Elem.{u2} α s) β (Subtype.instMeasurableSpace.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) m) mβ (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f)) -> (Measurable.{u2, u1} (Set.Elem.{u2} α (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) β (Subtype.instMeasurableSpace.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) m) mβ (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) f)) -> (Measurable.{u2, u1} α β m mβ f)
Case conversion may be inaccurate. Consider using '#align measurable_of_restrict_of_restrict_compl measurable_of_restrict_of_restrict_complₓ'. -/
theorem measurable_of_restrict_of_restrict_compl {f : α → β} {s : Set α} (hs : MeasurableSet s)
    (h₁ : Measurable (s.restrict f)) (h₂ : Measurable (sᶜ.restrict f)) : Measurable f :=
  measurable_of_measurable_union_cover s (sᶜ) hs hs.compl (union_compl_self s).ge h₁ h₂
#align measurable_of_restrict_of_restrict_compl measurable_of_restrict_of_restrict_compl

/- warning: measurable.dite -> Measurable.dite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} [_inst_1 : forall (x : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)] {f : (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β}, (Measurable.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) m) mβ f) -> (forall {g : (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) -> β}, (Measurable.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) β (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) m) mβ g) -> (MeasurableSet.{u1} α m s) -> (Measurable.{u1, u2} α β m mβ (fun (x : α) => dite.{succ u2} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (_inst_1 x) (fun (hx : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => f (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) x hx)) (fun (hx : Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) => g (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) x hx)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} [_inst_1 : forall (x : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)] {f : (Set.Elem.{u2} α s) -> β}, (Measurable.{u2, u1} (Set.Elem.{u2} α s) β (Subtype.instMeasurableSpace.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) m) mβ f) -> (forall {g : (Set.Elem.{u2} α (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) -> β}, (Measurable.{u2, u1} (Set.Elem.{u2} α (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) β (Subtype.instMeasurableSpace.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) m) mβ g) -> (MeasurableSet.{u2} α m s) -> (Measurable.{u2, u1} α β m mβ (fun (x : α) => dite.{succ u1} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (_inst_1 x) (fun (hx : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => f (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x hx)) (fun (hx : Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) => g (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) x hx)))))
Case conversion may be inaccurate. Consider using '#align measurable.dite Measurable.diteₓ'. -/
theorem Measurable.dite [∀ x, Decidable (x ∈ s)] {f : s → β} (hf : Measurable f) {g : sᶜ → β}
    (hg : Measurable g) (hs : MeasurableSet s) :
    Measurable fun x => if hx : x ∈ s then f ⟨x, hx⟩ else g ⟨x, hx⟩ :=
  measurable_of_restrict_of_restrict_compl hs (by simpa) (by simpa)
#align measurable.dite Measurable.dite

/- warning: measurable_of_measurable_on_compl_finite -> measurable_of_measurable_on_compl_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} [_inst_1 : MeasurableSingletonClass.{u1} α m] {f : α -> β} (s : Set.{u1} α), (Set.Finite.{u1} α s) -> (Measurable.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) β (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) m) mβ (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) f)) -> (Measurable.{u1, u2} α β m mβ f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} [_inst_1 : MeasurableSingletonClass.{u2} α m] {f : α -> β} (s : Set.{u2} α), (Set.Finite.{u2} α s) -> (Measurable.{u2, u1} (Set.Elem.{u2} α (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) β (Subtype.instMeasurableSpace.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) m) mβ (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) f)) -> (Measurable.{u2, u1} α β m mβ f)
Case conversion may be inaccurate. Consider using '#align measurable_of_measurable_on_compl_finite measurable_of_measurable_on_compl_finiteₓ'. -/
theorem measurable_of_measurable_on_compl_finite [MeasurableSingletonClass α] {f : α → β}
    (s : Set α) (hs : s.Finite) (hf : Measurable (sᶜ.restrict f)) : Measurable f :=
  letI : Fintype s := finite.fintype hs
  measurable_of_restrict_of_restrict_compl hs.measurable_set (measurable_of_finite _) hf
#align measurable_of_measurable_on_compl_finite measurable_of_measurable_on_compl_finite

/- warning: measurable_of_measurable_on_compl_singleton -> measurable_of_measurable_on_compl_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} [_inst_1 : MeasurableSingletonClass.{u1} α m] {f : α -> β} (a : α), (Measurable.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (setOf.{u1} α (fun (x : α) => Ne.{succ u1} α x a))) β (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (setOf.{u1} α (fun (x : α) => Ne.{succ u1} α x a))) m) mβ (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) (setOf.{u1} α (fun (x : α) => Ne.{succ u1} α x a)) f)) -> (Measurable.{u1, u2} α β m mβ f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} [_inst_1 : MeasurableSingletonClass.{u2} α m] {f : α -> β} (a : α), (Measurable.{u2, u1} (Set.Elem.{u2} α (setOf.{u2} α (fun (x : α) => Ne.{succ u2} α x a))) β (Subtype.instMeasurableSpace.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (setOf.{u2} α (fun (x : α) => Ne.{succ u2} α x a))) m) mβ (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) (setOf.{u2} α (fun (x : α) => Ne.{succ u2} α x a)) f)) -> (Measurable.{u2, u1} α β m mβ f)
Case conversion may be inaccurate. Consider using '#align measurable_of_measurable_on_compl_singleton measurable_of_measurable_on_compl_singletonₓ'. -/
theorem measurable_of_measurable_on_compl_singleton [MeasurableSingletonClass α] {f : α → β} (a : α)
    (hf : Measurable ({ x | x ≠ a }.restrict f)) : Measurable f :=
  measurable_of_measurable_on_compl_finite {a} (finite_singleton a) hf
#align measurable_of_measurable_on_compl_singleton measurable_of_measurable_on_compl_singleton

end Subtype

section Prod

#print MeasurableSpace.prod /-
/-- A `measurable_space` structure on the product of two measurable spaces. -/
def MeasurableSpace.prod {α β} (m₁ : MeasurableSpace α) (m₂ : MeasurableSpace β) :
    MeasurableSpace (α × β) :=
  m₁.comap Prod.fst ⊔ m₂.comap Prod.snd
#align measurable_space.prod MeasurableSpace.prod
-/

instance {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β] : MeasurableSpace (α × β) :=
  m₁.Prod m₂

/- warning: measurable_fst -> measurable_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ma : MeasurableSpace.{u1} α} {mb : MeasurableSpace.{u2} β}, Measurable.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.instMeasurableSpace.{u1, u2} α β ma mb) ma (Prod.fst.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ma : MeasurableSpace.{u2} α} {mb : MeasurableSpace.{u1} β}, Measurable.{max u2 u1, u2} (Prod.{u2, u1} α β) α (Prod.instMeasurableSpace.{u2, u1} α β ma mb) ma (Prod.fst.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align measurable_fst measurable_fstₓ'. -/
@[measurability]
theorem measurable_fst {ma : MeasurableSpace α} {mb : MeasurableSpace β} :
    Measurable (Prod.fst : α × β → α) :=
  Measurable.of_comap_le le_sup_left
#align measurable_fst measurable_fst

/- warning: measurable_snd -> measurable_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ma : MeasurableSpace.{u1} α} {mb : MeasurableSpace.{u2} β}, Measurable.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.instMeasurableSpace.{u1, u2} α β ma mb) mb (Prod.snd.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ma : MeasurableSpace.{u2} α} {mb : MeasurableSpace.{u1} β}, Measurable.{max u2 u1, u1} (Prod.{u2, u1} α β) β (Prod.instMeasurableSpace.{u2, u1} α β ma mb) mb (Prod.snd.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align measurable_snd measurable_sndₓ'. -/
@[measurability]
theorem measurable_snd {ma : MeasurableSpace α} {mb : MeasurableSpace β} :
    Measurable (Prod.snd : α × β → β) :=
  Measurable.of_comap_le le_sup_right
#align measurable_snd measurable_snd

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

include m mβ mγ

/- warning: measurable.fst -> Measurable.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {mγ : MeasurableSpace.{u3} γ} {f : α -> (Prod.{u2, u3} β γ)}, (Measurable.{u1, max u2 u3} α (Prod.{u2, u3} β γ) m (Prod.instMeasurableSpace.{u2, u3} β γ mβ mγ) f) -> (Measurable.{u1, u2} α β m mβ (fun (a : α) => Prod.fst.{u2, u3} β γ (f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u3} β} {mγ : MeasurableSpace.{u2} γ} {f : α -> (Prod.{u3, u2} β γ)}, (Measurable.{u1, max u3 u2} α (Prod.{u3, u2} β γ) m (Prod.instMeasurableSpace.{u3, u2} β γ mβ mγ) f) -> (Measurable.{u1, u3} α β m mβ (fun (a : α) => Prod.fst.{u3, u2} β γ (f a)))
Case conversion may be inaccurate. Consider using '#align measurable.fst Measurable.fstₓ'. -/
theorem Measurable.fst {f : α → β × γ} (hf : Measurable f) : Measurable fun a : α => (f a).1 :=
  measurable_fst.comp hf
#align measurable.fst Measurable.fst

/- warning: measurable.snd -> Measurable.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {mγ : MeasurableSpace.{u3} γ} {f : α -> (Prod.{u2, u3} β γ)}, (Measurable.{u1, max u2 u3} α (Prod.{u2, u3} β γ) m (Prod.instMeasurableSpace.{u2, u3} β γ mβ mγ) f) -> (Measurable.{u1, u3} α γ m mγ (fun (a : α) => Prod.snd.{u2, u3} β γ (f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u3} β} {mγ : MeasurableSpace.{u2} γ} {f : α -> (Prod.{u3, u2} β γ)}, (Measurable.{u1, max u3 u2} α (Prod.{u3, u2} β γ) m (Prod.instMeasurableSpace.{u3, u2} β γ mβ mγ) f) -> (Measurable.{u1, u2} α γ m mγ (fun (a : α) => Prod.snd.{u3, u2} β γ (f a)))
Case conversion may be inaccurate. Consider using '#align measurable.snd Measurable.sndₓ'. -/
theorem Measurable.snd {f : α → β × γ} (hf : Measurable f) : Measurable fun a : α => (f a).2 :=
  measurable_snd.comp hf
#align measurable.snd Measurable.snd

/- warning: measurable.prod -> Measurable.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {mγ : MeasurableSpace.{u3} γ} {f : α -> (Prod.{u2, u3} β γ)}, (Measurable.{u1, u2} α β m mβ (fun (a : α) => Prod.fst.{u2, u3} β γ (f a))) -> (Measurable.{u1, u3} α γ m mγ (fun (a : α) => Prod.snd.{u2, u3} β γ (f a))) -> (Measurable.{u1, max u2 u3} α (Prod.{u2, u3} β γ) m (Prod.instMeasurableSpace.{u2, u3} β γ mβ mγ) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u3} β} {mγ : MeasurableSpace.{u2} γ} {f : α -> (Prod.{u3, u2} β γ)}, (Measurable.{u1, u3} α β m mβ (fun (a : α) => Prod.fst.{u3, u2} β γ (f a))) -> (Measurable.{u1, u2} α γ m mγ (fun (a : α) => Prod.snd.{u3, u2} β γ (f a))) -> (Measurable.{u1, max u3 u2} α (Prod.{u3, u2} β γ) m (Prod.instMeasurableSpace.{u3, u2} β γ mβ mγ) f)
Case conversion may be inaccurate. Consider using '#align measurable.prod Measurable.prodₓ'. -/
@[measurability]
theorem Measurable.prod {f : α → β × γ} (hf₁ : Measurable fun a => (f a).1)
    (hf₂ : Measurable fun a => (f a).2) : Measurable f :=
  Measurable.of_le_map <|
    sup_le
      (by
        rw [MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.map_comp]
        exact hf₁)
      (by
        rw [MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.map_comp]
        exact hf₂)
#align measurable.prod Measurable.prod

/- warning: measurable.prod_mk -> Measurable.prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {β : Type.{u2}} {γ : Type.{u3}} {mβ : MeasurableSpace.{u2} β} {mγ : MeasurableSpace.{u3} γ} {f : α -> β} {g : α -> γ}, (Measurable.{u1, u2} α β m mβ f) -> (Measurable.{u1, u3} α γ m mγ g) -> (Measurable.{u1, max u2 u3} α (Prod.{u2, u3} β γ) m (Prod.instMeasurableSpace.{u2, u3} β γ mβ mγ) (fun (a : α) => Prod.mk.{u2, u3} β γ (f a) (g a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {β : Type.{u3}} {γ : Type.{u2}} {mβ : MeasurableSpace.{u3} β} {mγ : MeasurableSpace.{u2} γ} {f : α -> β} {g : α -> γ}, (Measurable.{u1, u3} α β m mβ f) -> (Measurable.{u1, u2} α γ m mγ g) -> (Measurable.{u1, max u2 u3} α (Prod.{u3, u2} β γ) m (Prod.instMeasurableSpace.{u3, u2} β γ mβ mγ) (fun (a : α) => Prod.mk.{u3, u2} β γ (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align measurable.prod_mk Measurable.prod_mkₓ'. -/
theorem Measurable.prod_mk {β γ} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {f : α → β}
    {g : α → γ} (hf : Measurable f) (hg : Measurable g) : Measurable fun a : α => (f a, g a) :=
  Measurable.prod hf hg
#align measurable.prod_mk Measurable.prod_mk

/- warning: measurable.prod_map -> Measurable.prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {mγ : MeasurableSpace.{u3} γ} [_inst_1 : MeasurableSpace.{u4} δ] {f : α -> β} {g : γ -> δ}, (Measurable.{u1, u2} α β m mβ f) -> (Measurable.{u3, u4} γ δ mγ _inst_1 g) -> (Measurable.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.instMeasurableSpace.{u1, u3} α γ m mγ) (Prod.instMeasurableSpace.{u2, u4} β δ mβ _inst_1) (Prod.map.{u1, u2, u3, u4} α β γ δ f g))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {δ : Type.{u4}} {m : MeasurableSpace.{u3} α} {mβ : MeasurableSpace.{u2} β} {mγ : MeasurableSpace.{u1} γ} [_inst_1 : MeasurableSpace.{u4} δ] {f : α -> β} {g : γ -> δ}, (Measurable.{u3, u2} α β m mβ f) -> (Measurable.{u1, u4} γ δ mγ _inst_1 g) -> (Measurable.{max u1 u3, max u4 u2} (Prod.{u3, u1} α γ) (Prod.{u2, u4} β δ) (Prod.instMeasurableSpace.{u3, u1} α γ m mγ) (Prod.instMeasurableSpace.{u2, u4} β δ mβ _inst_1) (Prod.map.{u3, u2, u1, u4} α β γ δ f g))
Case conversion may be inaccurate. Consider using '#align measurable.prod_map Measurable.prod_mapₓ'. -/
theorem Measurable.prod_map [MeasurableSpace δ] {f : α → β} {g : γ → δ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (Prod.map f g) :=
  (hf.comp measurable_fst).prod_mk (hg.comp measurable_snd)
#align measurable.prod_map Measurable.prod_map

omit mγ

#print measurable_prod_mk_left /-
theorem measurable_prod_mk_left {x : α} : Measurable (@Prod.mk _ β x) :=
  measurable_const.prod_mk measurable_id
#align measurable_prod_mk_left measurable_prod_mk_left
-/

/- warning: measurable_prod_mk_right -> measurable_prod_mk_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {y : β}, Measurable.{u1, max u1 u2} α (Prod.{u1, u2} α β) m (Prod.instMeasurableSpace.{u1, u2} α β m mβ) (fun (x : α) => Prod.mk.{u1, u2} α β x y)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} {y : β}, Measurable.{u2, max u1 u2} α (Prod.{u2, u1} α β) m (Prod.instMeasurableSpace.{u2, u1} α β m mβ) (fun (x : α) => Prod.mk.{u2, u1} α β x y)
Case conversion may be inaccurate. Consider using '#align measurable_prod_mk_right measurable_prod_mk_rightₓ'. -/
theorem measurable_prod_mk_right {y : β} : Measurable fun x : α => (x, y) :=
  measurable_id.prod_mk measurable_const
#align measurable_prod_mk_right measurable_prod_mk_right

include mγ

/- warning: measurable.of_uncurry_left -> Measurable.of_uncurry_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {mγ : MeasurableSpace.{u3} γ} {f : α -> β -> γ}, (Measurable.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.instMeasurableSpace.{u1, u2} α β m mβ) mγ (Function.uncurry.{u1, u2, u3} α β γ f)) -> (forall {x : α}, Measurable.{u2, u3} β γ mβ mγ (f x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u3} β} {mγ : MeasurableSpace.{u1} γ} {f : α -> β -> γ}, (Measurable.{max u3 u2, u1} (Prod.{u2, u3} α β) γ (Prod.instMeasurableSpace.{u2, u3} α β m mβ) mγ (Function.uncurry.{u2, u3, u1} α β γ f)) -> (forall {x : α}, Measurable.{u3, u1} β γ mβ mγ (f x))
Case conversion may be inaccurate. Consider using '#align measurable.of_uncurry_left Measurable.of_uncurry_leftₓ'. -/
theorem Measurable.of_uncurry_left {f : α → β → γ} (hf : Measurable (uncurry f)) {x : α} :
    Measurable (f x) :=
  hf.comp measurable_prod_mk_left
#align measurable.of_uncurry_left Measurable.of_uncurry_left

/- warning: measurable.of_uncurry_right -> Measurable.of_uncurry_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {mγ : MeasurableSpace.{u3} γ} {f : α -> β -> γ}, (Measurable.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.instMeasurableSpace.{u1, u2} α β m mβ) mγ (Function.uncurry.{u1, u2, u3} α β γ f)) -> (forall {y : β}, Measurable.{u1, u3} α γ m mγ (fun (x : α) => f x y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u3} β} {mγ : MeasurableSpace.{u1} γ} {f : α -> β -> γ}, (Measurable.{max u3 u2, u1} (Prod.{u2, u3} α β) γ (Prod.instMeasurableSpace.{u2, u3} α β m mβ) mγ (Function.uncurry.{u2, u3, u1} α β γ f)) -> (forall {y : β}, Measurable.{u2, u1} α γ m mγ (fun (x : α) => f x y))
Case conversion may be inaccurate. Consider using '#align measurable.of_uncurry_right Measurable.of_uncurry_rightₓ'. -/
theorem Measurable.of_uncurry_right {f : α → β → γ} (hf : Measurable (uncurry f)) {y : β} :
    Measurable fun x => f x y :=
  hf.comp measurable_prod_mk_right
#align measurable.of_uncurry_right Measurable.of_uncurry_right

/- warning: measurable_prod -> measurable_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {mγ : MeasurableSpace.{u3} γ} {f : α -> (Prod.{u2, u3} β γ)}, Iff (Measurable.{u1, max u2 u3} α (Prod.{u2, u3} β γ) m (Prod.instMeasurableSpace.{u2, u3} β γ mβ mγ) f) (And (Measurable.{u1, u2} α β m mβ (fun (a : α) => Prod.fst.{u2, u3} β γ (f a))) (Measurable.{u1, u3} α γ m mγ (fun (a : α) => Prod.snd.{u2, u3} β γ (f a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u3} β} {mγ : MeasurableSpace.{u2} γ} {f : α -> (Prod.{u3, u2} β γ)}, Iff (Measurable.{u1, max u3 u2} α (Prod.{u3, u2} β γ) m (Prod.instMeasurableSpace.{u3, u2} β γ mβ mγ) f) (And (Measurable.{u1, u3} α β m mβ (fun (a : α) => Prod.fst.{u3, u2} β γ (f a))) (Measurable.{u1, u2} α γ m mγ (fun (a : α) => Prod.snd.{u3, u2} β γ (f a))))
Case conversion may be inaccurate. Consider using '#align measurable_prod measurable_prodₓ'. -/
theorem measurable_prod {f : α → β × γ} :
    Measurable f ↔ (Measurable fun a => (f a).1) ∧ Measurable fun a => (f a).2 :=
  ⟨fun hf => ⟨measurable_fst.comp hf, measurable_snd.comp hf⟩, fun h => Measurable.prod h.1 h.2⟩
#align measurable_prod measurable_prod

omit mγ

/- warning: measurable_swap -> measurable_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β}, Measurable.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.instMeasurableSpace.{u1, u2} α β m mβ) (Prod.instMeasurableSpace.{u2, u1} β α mβ m) (Prod.swap.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β}, Measurable.{max u2 u1, max u2 u1} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (Prod.instMeasurableSpace.{u2, u1} α β m mβ) (Prod.instMeasurableSpace.{u1, u2} β α mβ m) (Prod.swap.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align measurable_swap measurable_swapₓ'. -/
@[measurability]
theorem measurable_swap : Measurable (Prod.swap : α × β → β × α) :=
  Measurable.prod measurable_snd measurable_fst
#align measurable_swap measurable_swap

/- warning: measurable_swap_iff -> measurable_swap_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {mγ : MeasurableSpace.{u3} γ} {f : (Prod.{u1, u2} α β) -> γ}, Iff (Measurable.{max u2 u1, u3} (Prod.{u2, u1} β α) γ (Prod.instMeasurableSpace.{u2, u1} β α mβ m) mγ (Function.comp.{succ (max u2 u1), max (succ u1) (succ u2), succ u3} (Prod.{u2, u1} β α) (Prod.{u1, u2} α β) γ f (Prod.swap.{u2, u1} β α))) (Measurable.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.instMeasurableSpace.{u1, u2} α β m mβ) mγ f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} {mγ : MeasurableSpace.{u3} γ} {f : (Prod.{u2, u1} α β) -> γ}, Iff (Measurable.{max u2 u1, u3} (Prod.{u1, u2} β α) γ (Prod.instMeasurableSpace.{u1, u2} β α mβ m) mγ (Function.comp.{succ (max u2 u1), max (succ u2) (succ u1), succ u3} (Prod.{u1, u2} β α) (Prod.{u2, u1} α β) γ f (Prod.swap.{u1, u2} β α))) (Measurable.{max u2 u1, u3} (Prod.{u2, u1} α β) γ (Prod.instMeasurableSpace.{u2, u1} α β m mβ) mγ f)
Case conversion may be inaccurate. Consider using '#align measurable_swap_iff measurable_swap_iffₓ'. -/
theorem measurable_swap_iff {mγ : MeasurableSpace γ} {f : α × β → γ} :
    Measurable (f ∘ Prod.swap) ↔ Measurable f :=
  ⟨fun hf => by
    convert hf.comp measurable_swap
    ext ⟨x, y⟩
    rfl, fun hf => hf.comp measurable_swap⟩
#align measurable_swap_iff measurable_swap_iff

/- warning: measurable_set.prod -> MeasurableSet.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {s : Set.{u1} α} {t : Set.{u2} β}, (MeasurableSet.{u1} α m s) -> (MeasurableSet.{u2} β mβ t) -> (MeasurableSet.{max u1 u2} (Prod.{u1, u2} α β) (Prod.instMeasurableSpace.{u1, u2} α β m mβ) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} {s : Set.{u2} α} {t : Set.{u1} β}, (MeasurableSet.{u2} α m s) -> (MeasurableSet.{u1} β mβ t) -> (MeasurableSet.{max u1 u2} (Prod.{u2, u1} α β) (Prod.instMeasurableSpace.{u2, u1} α β m mβ) (Set.prod.{u2, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align measurable_set.prod MeasurableSet.prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[measurability]
theorem MeasurableSet.prod {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ×ˢ t) :=
  MeasurableSet.inter (measurable_fst hs) (measurable_snd ht)
#align measurable_set.prod MeasurableSet.prod

/- warning: measurable_set_prod_of_nonempty -> measurableSet_prod_of_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {s : Set.{u1} α} {t : Set.{u2} β}, (Set.Nonempty.{max u1 u2} (Prod.{u1, u2} α β) (Set.prod.{u1, u2} α β s t)) -> (Iff (MeasurableSet.{max u1 u2} (Prod.{u1, u2} α β) (Prod.instMeasurableSpace.{u1, u2} α β m mβ) (Set.prod.{u1, u2} α β s t)) (And (MeasurableSet.{u1} α m s) (MeasurableSet.{u2} β mβ t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} {s : Set.{u2} α} {t : Set.{u1} β}, (Set.Nonempty.{max u2 u1} (Prod.{u2, u1} α β) (Set.prod.{u2, u1} α β s t)) -> (Iff (MeasurableSet.{max u1 u2} (Prod.{u2, u1} α β) (Prod.instMeasurableSpace.{u2, u1} α β m mβ) (Set.prod.{u2, u1} α β s t)) (And (MeasurableSet.{u2} α m s) (MeasurableSet.{u1} β mβ t)))
Case conversion may be inaccurate. Consider using '#align measurable_set_prod_of_nonempty measurableSet_prod_of_nonemptyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem measurableSet_prod_of_nonempty {s : Set α} {t : Set β} (h : (s ×ˢ t).Nonempty) :
    MeasurableSet (s ×ˢ t) ↔ MeasurableSet s ∧ MeasurableSet t :=
  by
  rcases h with ⟨⟨x, y⟩, hx, hy⟩
  refine' ⟨fun hst => _, fun h => h.1.Prod h.2⟩
  have : MeasurableSet ((fun x => (x, y)) ⁻¹' s ×ˢ t) := measurable_prod_mk_right hst
  have : MeasurableSet (Prod.mk x ⁻¹' s ×ˢ t) := measurable_prod_mk_left hst
  simp_all
#align measurable_set_prod_of_nonempty measurableSet_prod_of_nonempty

/- warning: measurable_set_prod -> measurableSet_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {s : Set.{u1} α} {t : Set.{u2} β}, Iff (MeasurableSet.{max u1 u2} (Prod.{u1, u2} α β) (Prod.instMeasurableSpace.{u1, u2} α β m mβ) (Set.prod.{u1, u2} α β s t)) (Or (And (MeasurableSet.{u1} α m s) (MeasurableSet.{u2} β mβ t)) (Or (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Eq.{succ u2} (Set.{u2} β) t (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} {s : Set.{u2} α} {t : Set.{u1} β}, Iff (MeasurableSet.{max u1 u2} (Prod.{u2, u1} α β) (Prod.instMeasurableSpace.{u2, u1} α β m mβ) (Set.prod.{u2, u1} α β s t)) (Or (And (MeasurableSet.{u2} α m s) (MeasurableSet.{u1} β mβ t)) (Or (Eq.{succ u2} (Set.{u2} α) s (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (Eq.{succ u1} (Set.{u1} β) t (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β)))))
Case conversion may be inaccurate. Consider using '#align measurable_set_prod measurableSet_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem measurableSet_prod {s : Set α} {t : Set β} :
    MeasurableSet (s ×ˢ t) ↔ MeasurableSet s ∧ MeasurableSet t ∨ s = ∅ ∨ t = ∅ :=
  by
  cases' (s ×ˢ t).eq_empty_or_nonempty with h h
  · simp [h, prod_eq_empty_iff.mp h]
  · simp [← not_nonempty_iff_eq_empty, prod_nonempty_iff.mp h, measurableSet_prod_of_nonempty h]
#align measurable_set_prod measurableSet_prod

#print measurableSet_swap_iff /-
theorem measurableSet_swap_iff {s : Set (α × β)} :
    MeasurableSet (Prod.swap ⁻¹' s) ↔ MeasurableSet s :=
  ⟨fun hs => by
    convert measurable_swap hs
    ext ⟨x, y⟩
    rfl, fun hs => measurable_swap hs⟩
#align measurable_set_swap_iff measurableSet_swap_iff
-/

instance [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α × β) :=
  ⟨fun ⟨a, b⟩ =>
    @singleton_prod_singleton _ _ a b ▸
      (measurableSet_singleton a).Prod (measurableSet_singleton b)⟩

/- warning: measurable_from_prod_countable -> measurable_from_prod_countable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} [_inst_1 : Countable.{succ u2} β] [_inst_2 : MeasurableSingletonClass.{u2} β mβ] {mγ : MeasurableSpace.{u3} γ} {f : (Prod.{u1, u2} α β) -> γ}, (forall (y : β), Measurable.{u1, u3} α γ m mγ (fun (x : α) => f (Prod.mk.{u1, u2} α β x y))) -> (Measurable.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.instMeasurableSpace.{u1, u2} α β m mβ) mγ f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u3} β} [_inst_1 : Countable.{succ u3} β] [_inst_2 : MeasurableSingletonClass.{u3} β mβ] {mγ : MeasurableSpace.{u2} γ} {f : (Prod.{u1, u3} α β) -> γ}, (forall (y : β), Measurable.{u1, u2} α γ m mγ (fun (x : α) => f (Prod.mk.{u1, u3} α β x y))) -> (Measurable.{max u1 u3, u2} (Prod.{u1, u3} α β) γ (Prod.instMeasurableSpace.{u1, u3} α β m mβ) mγ f)
Case conversion may be inaccurate. Consider using '#align measurable_from_prod_countable measurable_from_prod_countableₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem measurable_from_prod_countable [Countable β] [MeasurableSingletonClass β]
    {mγ : MeasurableSpace γ} {f : α × β → γ} (hf : ∀ y, Measurable fun x => f (x, y)) :
    Measurable f := by
  intro s hs
  have : f ⁻¹' s = ⋃ y, ((fun x => f (x, y)) ⁻¹' s) ×ˢ ({y} : Set β) :=
    by
    ext1 ⟨x, y⟩
    simp [and_assoc', and_left_comm]
  rw [this]
  exact MeasurableSet.iUnion fun y => (hf y hs).Prod (measurable_set_singleton y)
#align measurable_from_prod_countable measurable_from_prod_countable

/- warning: measurable.find -> Measurable.find is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {mβ : MeasurableSpace.{u2} β} {m : MeasurableSpace.{u1} α} {f : Nat -> α -> β} {p : Nat -> α -> Prop} [_inst_1 : forall (n : Nat), DecidablePred.{succ u1} α (p n)], (forall (n : Nat), Measurable.{u1, u2} α β m mβ (f n)) -> (forall (n : Nat), MeasurableSet.{u1} α m (setOf.{u1} α (fun (x : α) => p n x))) -> (forall (h : forall (x : α), Exists.{1} Nat (fun (n : Nat) => p n x)), Measurable.{u1, u2} α β m mβ (fun (x : α) => f (Nat.find (fun (n : Nat) => p n x) (fun (a : Nat) => _inst_1 a x) (h x)) x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {mβ : MeasurableSpace.{u1} β} {m : MeasurableSpace.{u2} α} {f : Nat -> α -> β} {p : Nat -> α -> Prop} [_inst_1 : forall (n : Nat), DecidablePred.{succ u2} α (p n)], (forall (n : Nat), Measurable.{u2, u1} α β m mβ (f n)) -> (forall (n : Nat), MeasurableSet.{u2} α m (setOf.{u2} α (fun (x : α) => p n x))) -> (forall (h : forall (x : α), Exists.{1} Nat (fun (n : Nat) => p n x)), Measurable.{u2, u1} α β m mβ (fun (x : α) => f (Nat.find (fun (n : Nat) => p n x) (fun (a : Nat) => _inst_1 a x) (h x)) x))
Case conversion may be inaccurate. Consider using '#align measurable.find Measurable.findₓ'. -/
/-- A piecewise function on countably many pieces is measurable if all the data is measurable. -/
@[measurability]
theorem Measurable.find {m : MeasurableSpace α} {f : ℕ → α → β} {p : ℕ → α → Prop}
    [∀ n, DecidablePred (p n)] (hf : ∀ n, Measurable (f n)) (hp : ∀ n, MeasurableSet { x | p n x })
    (h : ∀ x, ∃ n, p n x) : Measurable fun x => f (Nat.find (h x)) x :=
  haveI : Measurable fun p : α × ℕ => f p.2 p.1 := measurable_from_prod_countable fun n => hf n
  this.comp (Measurable.prod_mk measurable_id (measurable_find h hp))
#align measurable.find Measurable.find

/- warning: exists_measurable_piecewise_nat -> exists_measurable_piecewise_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {mβ : MeasurableSpace.{u2} β} {m : MeasurableSpace.{u1} α} (t : Nat -> (Set.{u2} β)), (forall (n : Nat), MeasurableSet.{u2} β mβ (t n)) -> (Pairwise.{0} Nat (Function.onFun.{1, succ u2, 1} Nat (Set.{u2} β) Prop (Disjoint.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))) t)) -> (forall (g : Nat -> β -> α), (forall (n : Nat), Measurable.{u2, u1} β α mβ m (g n)) -> (Exists.{max (succ u2) (succ u1)} (β -> α) (fun (f : β -> α) => And (Measurable.{u2, u1} β α mβ m f) (forall (n : Nat) (x : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (t n)) -> (Eq.{succ u1} α (f x) (g n x))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {mβ : MeasurableSpace.{u1} β} {m : MeasurableSpace.{u2} α} (t : Nat -> (Set.{u1} β)), (forall (n : Nat), MeasurableSet.{u1} β mβ (t n)) -> (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} β) Prop (Disjoint.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} β) (Preorder.toLE.{u1} (Set.{u1} β) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) t)) -> (forall (g : Nat -> β -> α), (forall (n : Nat), Measurable.{u1, u2} β α mβ m (g n)) -> (Exists.{max (succ u2) (succ u1)} (β -> α) (fun (f : β -> α) => And (Measurable.{u1, u2} β α mβ m f) (forall (n : Nat) (x : β), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (t n)) -> (Eq.{succ u2} α (f x) (g n x))))))
Case conversion may be inaccurate. Consider using '#align exists_measurable_piecewise_nat exists_measurable_piecewise_natₓ'. -/
/-- Given countably many disjoint measurable sets `t n` and countably many measurable
functions `g n`, one can construct a measurable function that coincides with `g n` on `t n`. -/
theorem exists_measurable_piecewise_nat {m : MeasurableSpace α} (t : ℕ → Set β)
    (t_meas : ∀ n, MeasurableSet (t n)) (t_disj : Pairwise (Disjoint on t)) (g : ℕ → β → α)
    (hg : ∀ n, Measurable (g n)) : ∃ f : β → α, Measurable f ∧ ∀ n x, x ∈ t n → f x = g n x := by
  classical
    let p : ℕ → β → Prop := fun n x => x ∈ t n ∪ (⋃ k, t k)ᶜ
    have M : ∀ n, MeasurableSet { x | p n x } := fun n =>
      (t_meas n).union (MeasurableSet.compl (MeasurableSet.iUnion t_meas))
    have P : ∀ x, ∃ n, p n x := by
      intro x
      by_cases H : ∀ i : ℕ, x ∉ t i
      · exact ⟨0, Or.inr (by simpa only [mem_Inter, compl_Union] using H)⟩
      · simp only [not_forall, not_not_mem] at H
        rcases H with ⟨n, hn⟩
        exact ⟨n, Or.inl hn⟩
    refine' ⟨fun x => g (Nat.find (P x)) x, Measurable.find hg M P, _⟩
    intro n x hx
    have : x ∈ t (Nat.find (P x)) :=
      by
      have B : x ∈ t (Nat.find (P x)) ∪ (⋃ k, t k)ᶜ := Nat.find_spec (P x)
      have B' : (∀ i : ℕ, x ∉ t i) ↔ False :=
        by
        simp only [iff_false_iff, not_forall, not_not_mem]
        exact ⟨n, hx⟩
      simpa only [B', mem_union, mem_Inter, or_false_iff, compl_Union, mem_compl_iff] using B
    congr
    by_contra h
    exact (t_disj (Ne.symm h)).le_bot ⟨hx, this⟩
#align exists_measurable_piecewise_nat exists_measurable_piecewise_nat

end Prod

section Pi

variable {π : δ → Type _} [MeasurableSpace α]

#print MeasurableSpace.pi /-
instance MeasurableSpace.pi [m : ∀ a, MeasurableSpace (π a)] : MeasurableSpace (∀ a, π a) :=
  ⨆ a, (m a).comap fun b => b a
#align measurable_space.pi MeasurableSpace.pi
-/

variable [∀ a, MeasurableSpace (π a)] [MeasurableSpace γ]

/- warning: measurable_pi_iff -> measurable_pi_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : Type.{u2}} {π : δ -> Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : forall (a : δ), MeasurableSpace.{u3} (π a)] {g : α -> (forall (a : δ), π a)}, Iff (Measurable.{u1, max u2 u3} α (forall (a : δ), π a) _inst_1 (MeasurableSpace.pi.{u2, u3} δ (fun (a : δ) => π a) (fun (a : δ) => _inst_2 a)) g) (forall (a : δ), Measurable.{u1, u3} α (π a) _inst_1 (_inst_2 a) (fun (x : α) => g x a))
but is expected to have type
  forall {α : Type.{u3}} {δ : Type.{u2}} {π : δ -> Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] [_inst_2 : forall (a : δ), MeasurableSpace.{u1} (π a)] {g : α -> (forall (a : δ), π a)}, Iff (Measurable.{u3, max u2 u1} α (forall (a : δ), π a) _inst_1 (MeasurableSpace.pi.{u2, u1} δ (fun (a : δ) => π a) (fun (a : δ) => _inst_2 a)) g) (forall (a : δ), Measurable.{u3, u1} α (π a) _inst_1 (_inst_2 a) (fun (x : α) => g x a))
Case conversion may be inaccurate. Consider using '#align measurable_pi_iff measurable_pi_iffₓ'. -/
theorem measurable_pi_iff {g : α → ∀ a, π a} : Measurable g ↔ ∀ a, Measurable fun x => g x a := by
  simp_rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp, iSup_le_iff]
#align measurable_pi_iff measurable_pi_iff

/- warning: measurable_pi_apply -> measurable_pi_apply is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u1}} {π : δ -> Type.{u2}} [_inst_2 : forall (a : δ), MeasurableSpace.{u2} (π a)] (a : δ), Measurable.{max u1 u2, u2} (forall (a : δ), π a) (π a) (MeasurableSpace.pi.{u1, u2} δ (fun (a : δ) => π a) (fun (a : δ) => _inst_2 a)) (_inst_2 a) (fun (f : forall (a : δ), π a) => f a)
but is expected to have type
  forall {δ : Type.{u2}} {π : δ -> Type.{u1}} [_inst_2 : forall (a : δ), MeasurableSpace.{u1} (π a)] (a : δ), Measurable.{max u2 u1, u1} (forall (a : δ), π a) (π a) (MeasurableSpace.pi.{u2, u1} δ (fun (a : δ) => π a) (fun (a : δ) => _inst_2 a)) (_inst_2 a) (fun (f : forall (a : δ), π a) => f a)
Case conversion may be inaccurate. Consider using '#align measurable_pi_apply measurable_pi_applyₓ'. -/
@[measurability]
theorem measurable_pi_apply (a : δ) : Measurable fun f : ∀ a, π a => f a :=
  Measurable.of_comap_le <| le_iSup _ a
#align measurable_pi_apply measurable_pi_apply

/- warning: measurable.eval -> Measurable.eval is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : Type.{u2}} {π : δ -> Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : forall (a : δ), MeasurableSpace.{u3} (π a)] {a : δ} {g : α -> (forall (a : δ), π a)}, (Measurable.{u1, max u2 u3} α (forall (a : δ), π a) _inst_1 (MeasurableSpace.pi.{u2, u3} δ (fun (a : δ) => π a) (fun (a : δ) => _inst_2 a)) g) -> (Measurable.{u1, u3} α (π a) _inst_1 (_inst_2 a) (fun (x : α) => g x a))
but is expected to have type
  forall {α : Type.{u3}} {δ : Type.{u2}} {π : δ -> Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] [_inst_2 : forall (a : δ), MeasurableSpace.{u1} (π a)] {a : δ} {g : α -> (forall (a : δ), π a)}, (Measurable.{u3, max u2 u1} α (forall (a : δ), π a) _inst_1 (MeasurableSpace.pi.{u2, u1} δ (fun (a : δ) => π a) (fun (a : δ) => _inst_2 a)) g) -> (Measurable.{u3, u1} α (π a) _inst_1 (_inst_2 a) (fun (x : α) => g x a))
Case conversion may be inaccurate. Consider using '#align measurable.eval Measurable.evalₓ'. -/
@[measurability]
theorem Measurable.eval {a : δ} {g : α → ∀ a, π a} (hg : Measurable g) :
    Measurable fun x => g x a :=
  (measurable_pi_apply a).comp hg
#align measurable.eval Measurable.eval

/- warning: measurable_pi_lambda -> measurable_pi_lambda is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : Type.{u2}} {π : δ -> Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : forall (a : δ), MeasurableSpace.{u3} (π a)] (f : α -> (forall (a : δ), π a)), (forall (a : δ), Measurable.{u1, u3} α (π a) _inst_1 (_inst_2 a) (fun (c : α) => f c a)) -> (Measurable.{u1, max u2 u3} α (forall (a : δ), π a) _inst_1 (MeasurableSpace.pi.{u2, u3} δ (fun (a : δ) => π a) (fun (a : δ) => _inst_2 a)) f)
but is expected to have type
  forall {α : Type.{u3}} {δ : Type.{u1}} {π : δ -> Type.{u2}} [_inst_1 : MeasurableSpace.{u3} α] [_inst_2 : forall (a : δ), MeasurableSpace.{u2} (π a)] (f : α -> (forall (a : δ), π a)), (forall (a : δ), Measurable.{u3, u2} α (π a) _inst_1 (_inst_2 a) (fun (c : α) => f c a)) -> (Measurable.{u3, max u1 u2} α (forall (a : δ), π a) _inst_1 (MeasurableSpace.pi.{u1, u2} δ (fun (a : δ) => π a) (fun (a : δ) => _inst_2 a)) f)
Case conversion may be inaccurate. Consider using '#align measurable_pi_lambda measurable_pi_lambdaₓ'. -/
@[measurability]
theorem measurable_pi_lambda (f : α → ∀ a, π a) (hf : ∀ a, Measurable fun c => f c a) :
    Measurable f :=
  measurable_pi_iff.mpr hf
#align measurable_pi_lambda measurable_pi_lambda

/- warning: measurable_update -> measurable_update is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u1}} {π : δ -> Type.{u2}} [_inst_2 : forall (a : δ), MeasurableSpace.{u2} (π a)] (f : forall (a : δ), π a) {a : δ} [_inst_4 : DecidableEq.{succ u1} δ], Measurable.{u2, max u1 u2} (π a) (forall (a : δ), π a) (_inst_2 a) (MeasurableSpace.pi.{u1, u2} δ (fun (a : δ) => π a) (fun (a : δ) => _inst_2 a)) (Function.update.{succ u1, succ u2} δ (fun (a : δ) => π a) (fun (a : δ) (b : δ) => _inst_4 a b) f a)
but is expected to have type
  forall {δ : Type.{u2}} {π : δ -> Type.{u1}} [_inst_2 : forall (a : δ), MeasurableSpace.{u1} (π a)] (f : forall (a : δ), π a) {a : δ} [_inst_4 : DecidableEq.{succ u2} δ], Measurable.{u1, max u2 u1} (π a) (forall (a : δ), π a) (_inst_2 a) (MeasurableSpace.pi.{u2, u1} δ (fun (a : δ) => π a) (fun (a : δ) => _inst_2 a)) (Function.update.{succ u2, succ u1} δ (fun (a : δ) => π a) (fun (a : δ) (b : δ) => _inst_4 a b) f a)
Case conversion may be inaccurate. Consider using '#align measurable_update measurable_updateₓ'. -/
/-- The function `update f a : π a → Π a, π a` is always measurable.
  This doesn't require `f` to be measurable.
  This should not be confused with the statement that `update f a x` is measurable. -/
@[measurability]
theorem measurable_update (f : ∀ a : δ, π a) {a : δ} [DecidableEq δ] : Measurable (update f a) :=
  by
  apply measurable_pi_lambda
  intro x; by_cases hx : x = a
  · cases hx
    convert measurable_id
    ext
    simp
  simp_rw [update_noteq hx]; apply measurable_const
#align measurable_update measurable_update

/- warning: measurable_set.pi -> MeasurableSet.pi is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u1}} {π : δ -> Type.{u2}} [_inst_2 : forall (a : δ), MeasurableSpace.{u2} (π a)] {s : Set.{u1} δ} {t : forall (i : δ), Set.{u2} (π i)}, (Set.Countable.{u1} δ s) -> (forall (i : δ), (Membership.Mem.{u1, u1} δ (Set.{u1} δ) (Set.hasMem.{u1} δ) i s) -> (MeasurableSet.{u2} (π i) (_inst_2 i) (t i))) -> (MeasurableSet.{max u1 u2} (forall (i : δ), π i) (MeasurableSpace.pi.{u1, u2} δ (fun (i : δ) => π i) (fun (a : δ) => _inst_2 a)) (Set.pi.{u1, u2} δ (fun (i : δ) => π i) s t))
but is expected to have type
  forall {δ : Type.{u2}} {π : δ -> Type.{u1}} [_inst_2 : forall (a : δ), MeasurableSpace.{u1} (π a)] {s : Set.{u2} δ} {t : forall (i : δ), Set.{u1} (π i)}, (Set.Countable.{u2} δ s) -> (forall (i : δ), (Membership.mem.{u2, u2} δ (Set.{u2} δ) (Set.instMembershipSet.{u2} δ) i s) -> (MeasurableSet.{u1} (π i) (_inst_2 i) (t i))) -> (MeasurableSet.{max u2 u1} (forall (i : δ), π i) (MeasurableSpace.pi.{u2, u1} δ (fun (i : δ) => π i) (fun (a : δ) => _inst_2 a)) (Set.pi.{u2, u1} δ (fun (i : δ) => π i) s t))
Case conversion may be inaccurate. Consider using '#align measurable_set.pi MeasurableSet.piₓ'. -/
/- Even though we cannot use projection notation, we still keep a dot to be consistent with similar
  lemmas, like `measurable_set.prod`. -/
@[measurability]
theorem MeasurableSet.pi {s : Set δ} {t : ∀ i : δ, Set (π i)} (hs : s.Countable)
    (ht : ∀ i ∈ s, MeasurableSet (t i)) : MeasurableSet (s.pi t) :=
  by
  rw [pi_def]
  exact MeasurableSet.biInter hs fun i hi => measurable_pi_apply _ (ht i hi)
#align measurable_set.pi MeasurableSet.pi

/- warning: measurable_set.univ_pi -> MeasurableSet.univ_pi is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u1}} {π : δ -> Type.{u2}} [_inst_2 : forall (a : δ), MeasurableSpace.{u2} (π a)] [_inst_4 : Countable.{succ u1} δ] {t : forall (i : δ), Set.{u2} (π i)}, (forall (i : δ), MeasurableSet.{u2} (π i) (_inst_2 i) (t i)) -> (MeasurableSet.{max u1 u2} (forall (i : δ), π i) (MeasurableSpace.pi.{u1, u2} δ (fun (i : δ) => π i) (fun (a : δ) => _inst_2 a)) (Set.pi.{u1, u2} δ (fun (i : δ) => π i) (Set.univ.{u1} δ) t))
but is expected to have type
  forall {δ : Type.{u2}} {π : δ -> Type.{u1}} [_inst_2 : forall (a : δ), MeasurableSpace.{u1} (π a)] [_inst_4 : Countable.{succ u2} δ] {t : forall (i : δ), Set.{u1} (π i)}, (forall (i : δ), MeasurableSet.{u1} (π i) (_inst_2 i) (t i)) -> (MeasurableSet.{max u1 u2} (forall (i : δ), π i) (MeasurableSpace.pi.{u2, u1} δ (fun (i : δ) => π i) (fun (a : δ) => _inst_2 a)) (Set.pi.{u2, u1} δ (fun (i : δ) => π i) (Set.univ.{u2} δ) t))
Case conversion may be inaccurate. Consider using '#align measurable_set.univ_pi MeasurableSet.univ_piₓ'. -/
theorem MeasurableSet.univ_pi [Countable δ] {t : ∀ i : δ, Set (π i)}
    (ht : ∀ i, MeasurableSet (t i)) : MeasurableSet (pi univ t) :=
  MeasurableSet.pi (to_countable _) fun i _ => ht i
#align measurable_set.univ_pi MeasurableSet.univ_pi

/- warning: measurable_set_pi_of_nonempty -> measurableSet_pi_of_nonempty is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u1}} {π : δ -> Type.{u2}} [_inst_2 : forall (a : δ), MeasurableSpace.{u2} (π a)] {s : Set.{u1} δ} {t : forall (i : δ), Set.{u2} (π i)}, (Set.Countable.{u1} δ s) -> (Set.Nonempty.{max u1 u2} (forall (i : δ), π i) (Set.pi.{u1, u2} δ (fun (i : δ) => π i) s t)) -> (Iff (MeasurableSet.{max u1 u2} (forall (i : δ), π i) (MeasurableSpace.pi.{u1, u2} δ (fun (i : δ) => π i) (fun (a : δ) => _inst_2 a)) (Set.pi.{u1, u2} δ (fun (i : δ) => π i) s t)) (forall (i : δ), (Membership.Mem.{u1, u1} δ (Set.{u1} δ) (Set.hasMem.{u1} δ) i s) -> (MeasurableSet.{u2} (π i) (_inst_2 i) (t i))))
but is expected to have type
  forall {δ : Type.{u2}} {π : δ -> Type.{u1}} [_inst_2 : forall (a : δ), MeasurableSpace.{u1} (π a)] {s : Set.{u2} δ} {t : forall (i : δ), Set.{u1} (π i)}, (Set.Countable.{u2} δ s) -> (Set.Nonempty.{max u2 u1} (forall (i : δ), π i) (Set.pi.{u2, u1} δ (fun (i : δ) => π i) s t)) -> (Iff (MeasurableSet.{max u1 u2} (forall (i : δ), π i) (MeasurableSpace.pi.{u2, u1} δ (fun (i : δ) => π i) (fun (a : δ) => _inst_2 a)) (Set.pi.{u2, u1} δ (fun (i : δ) => π i) s t)) (forall (i : δ), (Membership.mem.{u2, u2} δ (Set.{u2} δ) (Set.instMembershipSet.{u2} δ) i s) -> (MeasurableSet.{u1} (π i) (_inst_2 i) (t i))))
Case conversion may be inaccurate. Consider using '#align measurable_set_pi_of_nonempty measurableSet_pi_of_nonemptyₓ'. -/
theorem measurableSet_pi_of_nonempty {s : Set δ} {t : ∀ i, Set (π i)} (hs : s.Countable)
    (h : (pi s t).Nonempty) : MeasurableSet (pi s t) ↔ ∀ i ∈ s, MeasurableSet (t i) := by
  classical
    rcases h with ⟨f, hf⟩
    refine' ⟨fun hst i hi => _, MeasurableSet.pi hs⟩
    convert measurable_update f hst
    rw [update_preimage_pi hi]
    exact fun j hj _ => hf j hj
#align measurable_set_pi_of_nonempty measurableSet_pi_of_nonempty

/- warning: measurable_set_pi -> measurableSet_pi is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u1}} {π : δ -> Type.{u2}} [_inst_2 : forall (a : δ), MeasurableSpace.{u2} (π a)] {s : Set.{u1} δ} {t : forall (i : δ), Set.{u2} (π i)}, (Set.Countable.{u1} δ s) -> (Iff (MeasurableSet.{max u1 u2} (forall (i : δ), π i) (MeasurableSpace.pi.{u1, u2} δ (fun (i : δ) => π i) (fun (a : δ) => _inst_2 a)) (Set.pi.{u1, u2} δ (fun (i : δ) => π i) s t)) (Or (forall (i : δ), (Membership.Mem.{u1, u1} δ (Set.{u1} δ) (Set.hasMem.{u1} δ) i s) -> (MeasurableSet.{u2} (π i) (_inst_2 i) (t i))) (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : δ), π i)) (Set.pi.{u1, u2} δ (fun (i : δ) => π i) s t) (EmptyCollection.emptyCollection.{max u1 u2} (Set.{max u1 u2} (forall (i : δ), π i)) (Set.hasEmptyc.{max u1 u2} (forall (i : δ), π i))))))
but is expected to have type
  forall {δ : Type.{u2}} {π : δ -> Type.{u1}} [_inst_2 : forall (a : δ), MeasurableSpace.{u1} (π a)] {s : Set.{u2} δ} {t : forall (i : δ), Set.{u1} (π i)}, (Set.Countable.{u2} δ s) -> (Iff (MeasurableSet.{max u1 u2} (forall (i : δ), π i) (MeasurableSpace.pi.{u2, u1} δ (fun (i : δ) => π i) (fun (a : δ) => _inst_2 a)) (Set.pi.{u2, u1} δ (fun (i : δ) => π i) s t)) (Or (forall (i : δ), (Membership.mem.{u2, u2} δ (Set.{u2} δ) (Set.instMembershipSet.{u2} δ) i s) -> (MeasurableSet.{u1} (π i) (_inst_2 i) (t i))) (Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : δ), π i)) (Set.pi.{u2, u1} δ (fun (i : δ) => π i) s t) (EmptyCollection.emptyCollection.{max u2 u1} (Set.{max u2 u1} (forall (i : δ), π i)) (Set.instEmptyCollectionSet.{max u2 u1} (forall (i : δ), π i))))))
Case conversion may be inaccurate. Consider using '#align measurable_set_pi measurableSet_piₓ'. -/
theorem measurableSet_pi {s : Set δ} {t : ∀ i, Set (π i)} (hs : s.Countable) :
    MeasurableSet (pi s t) ↔ (∀ i ∈ s, MeasurableSet (t i)) ∨ pi s t = ∅ :=
  by
  cases' (pi s t).eq_empty_or_nonempty with h h
  · simp [h]
  · simp [measurableSet_pi_of_nonempty hs, h, ← not_nonempty_iff_eq_empty]
#align measurable_set_pi measurableSet_pi

instance [Countable δ] [∀ a, MeasurableSingletonClass (π a)] :
    MeasurableSingletonClass (∀ a, π a) :=
  ⟨fun f => univ_pi_singleton f ▸ MeasurableSet.univ_pi fun t => measurableSet_singleton (f t)⟩

variable (π)

/- warning: measurable_pi_equiv_pi_subtype_prod_symm -> measurable_piEquivPiSubtypeProd_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measurable_pi_equiv_pi_subtype_prod_symm measurable_piEquivPiSubtypeProd_symmₓ'. -/
@[measurability]
theorem measurable_piEquivPiSubtypeProd_symm (p : δ → Prop) [DecidablePred p] :
    Measurable (Equiv.piEquivPiSubtypeProd p π).symm :=
  by
  apply measurable_pi_iff.2 fun j => _
  by_cases hj : p j
  · simp only [hj, dif_pos, Equiv.piEquivPiSubtypeProd_symm_apply]
    have : Measurable fun f : ∀ i : { x // p x }, π ↑i => f ⟨j, hj⟩ := measurable_pi_apply ⟨j, hj⟩
    exact Measurable.comp this measurable_fst
  · simp only [hj, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg, not_false_iff]
    have : Measurable fun f : ∀ i : { x // ¬p x }, π ↑i => f ⟨j, hj⟩ := measurable_pi_apply ⟨j, hj⟩
    exact Measurable.comp this measurable_snd
#align measurable_pi_equiv_pi_subtype_prod_symm measurable_piEquivPiSubtypeProd_symm

/- warning: measurable_pi_equiv_pi_subtype_prod -> measurable_piEquivPiSubtypeProd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measurable_pi_equiv_pi_subtype_prod measurable_piEquivPiSubtypeProdₓ'. -/
@[measurability]
theorem measurable_piEquivPiSubtypeProd (p : δ → Prop) [DecidablePred p] :
    Measurable (Equiv.piEquivPiSubtypeProd p π) :=
  by
  refine' measurable_prod.2 _
  constructor <;>
    · apply measurable_pi_iff.2 fun j => _
      simp only [pi_equiv_pi_subtype_prod_apply, measurable_pi_apply]
#align measurable_pi_equiv_pi_subtype_prod measurable_piEquivPiSubtypeProd

end Pi

/- warning: tprod.measurable_space -> TProd.instMeasurableSpace is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u_4}} (π : δ -> Type.{u_1}) [_inst_1 : forall (x : δ), MeasurableSpace.{u_1} (π x)] (l : List.{u_4} δ), MeasurableSpace.{max u_1 u_2} (List.TProd.{u_4, u_1, u_2} δ π l)
but is expected to have type
  forall {δ : Type.{u_1}} (π : δ -> Type.{u_2}) [_inst_1 : forall (x : δ), MeasurableSpace.{u_2} (π x)] (l : List.{u_1} δ), MeasurableSpace.{u_2} (List.TProd.{u_1, u_2} δ π l)
Case conversion may be inaccurate. Consider using '#align tprod.measurable_space TProd.instMeasurableSpaceₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance TProd.instMeasurableSpace (π : δ → Type _) [∀ x, MeasurableSpace (π x)] :
    ∀ l : List δ, MeasurableSpace (List.TProd π l)
  | [] => PUnit.instMeasurableSpace
  | i::is => @Prod.instMeasurableSpace _ _ _ (TProd.instMeasurableSpace is)
#align tprod.measurable_space TProd.instMeasurableSpace

section Tprod

open List

variable {π : δ → Type _} [∀ x, MeasurableSpace (π x)]

/- warning: measurable_tprod_mk -> measurable_tProd_mk is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u_4}} {π : δ -> Type.{u_7}} [_inst_1 : forall (x : δ), MeasurableSpace.{u_7} (π x)] (l : List.{u_4} δ), Measurable.{max u_4 u_7, max u_7 u_1} (forall (i : δ), π i) (List.TProd.{u_4, u_7, u_1} δ π l) (MeasurableSpace.pi.{u_4, u_7} δ (fun (i : δ) => π i) (fun (x : δ) => _inst_1 x)) (TProd.instMeasurableSpace.{u_4, u_7, u_1} δ π (fun (x : δ) => _inst_1 x) l) (List.TProd.mk.{u_4, u_7, u_1} δ π l)
but is expected to have type
  forall {δ : Type.{u_1}} {π : δ -> Type.{u_2}} [_inst_1 : forall (x : δ), MeasurableSpace.{u_2} (π x)] (l : List.{u_1} δ), Measurable.{max u_1 u_2, u_2} (forall (i : δ), π i) (List.TProd.{u_1, u_2} δ π l) (MeasurableSpace.pi.{u_1, u_2} δ (fun (i : δ) => π i) (fun (x : δ) => _inst_1 x)) (TProd.instMeasurableSpace.{u_1, u_2} δ π (fun (x : δ) => _inst_1 x) l) (List.TProd.mk.{u_1, u_2} δ π l)
Case conversion may be inaccurate. Consider using '#align measurable_tprod_mk measurable_tProd_mkₓ'. -/
theorem measurable_tProd_mk (l : List δ) : Measurable (@TProd.mk δ π l) :=
  by
  induction' l with i l ih
  · exact measurable_const
  · exact (measurable_pi_apply i).prod_mk ih
#align measurable_tprod_mk measurable_tProd_mk

/- warning: measurable_tprod_elim -> measurable_tProd_elim is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u_4}} {π : δ -> Type.{u_7}} [_inst_1 : forall (x : δ), MeasurableSpace.{u_7} (π x)] [_inst_2 : DecidableEq.{succ u_4} δ] {l : List.{u_4} δ} {i : δ} (hi : Membership.Mem.{u_4, u_4} δ (List.{u_4} δ) (List.hasMem.{u_4} δ) i l), Measurable.{max u_7 u_1, u_7} (List.TProd.{u_4, u_7, u_1} δ π l) (π i) (TProd.instMeasurableSpace.{u_4, u_7, u_1} δ π (fun (x : δ) => _inst_1 x) l) (_inst_1 i) (fun (v : List.TProd.{u_4, u_7, u_1} δ π l) => List.TProd.elim.{u_4, u_7, u_1} δ π (fun (a : δ) (b : δ) => _inst_2 a b) l v i hi)
but is expected to have type
  forall {δ : Type.{u_1}} {π : δ -> Type.{u_2}} [_inst_1 : forall (x : δ), MeasurableSpace.{u_2} (π x)] [_inst_2 : DecidableEq.{succ u_1} δ] {l : List.{u_1} δ} {i : δ} (hi : Membership.mem.{u_1, u_1} δ (List.{u_1} δ) (List.instMembershipList.{u_1} δ) i l), Measurable.{u_2, u_2} (List.TProd.{u_1, u_2} δ π l) (π i) (TProd.instMeasurableSpace.{u_1, u_2} δ π (fun (x : δ) => _inst_1 x) l) (_inst_1 i) (fun (v : List.TProd.{u_1, u_2} δ π l) => List.TProd.elim.{u_1, u_2} δ π (fun (a : δ) (b : δ) => _inst_2 a b) l v i hi)
Case conversion may be inaccurate. Consider using '#align measurable_tprod_elim measurable_tProd_elimₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem measurable_tProd_elim [DecidableEq δ] :
    ∀ {l : List δ} {i : δ} (hi : i ∈ l), Measurable fun v : TProd π l => v.elim hi
  | i::is, j, hj => by
    by_cases hji : j = i
    · subst hji
      simp [measurable_fst]
    · rw [funext <| tprod.elim_of_ne _ hji]
      exact (measurable_tProd_elim (hj.resolve_left hji)).comp measurable_snd
#align measurable_tprod_elim measurable_tProd_elim

/- warning: measurable_tprod_elim' -> measurable_tProd_elim' is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u_4}} {π : δ -> Type.{u_7}} [_inst_1 : forall (x : δ), MeasurableSpace.{u_7} (π x)] [_inst_2 : DecidableEq.{succ u_4} δ] {l : List.{u_4} δ} (h : forall (i : δ), Membership.Mem.{u_4, u_4} δ (List.{u_4} δ) (List.hasMem.{u_4} δ) i l), Measurable.{max u_7 u_1, max u_4 u_7} (List.TProd.{u_4, u_7, u_1} δ π l) (forall (i : δ), π i) (TProd.instMeasurableSpace.{u_4, u_7, u_1} δ π (fun (a : δ) => _inst_1 a) l) (MeasurableSpace.pi.{u_4, u_7} δ (fun (i : δ) => π i) (fun (a : δ) => _inst_1 a)) (List.TProd.elim'.{u_4, u_7, u_1} δ π l (fun (a : δ) (b : δ) => _inst_2 a b) h)
but is expected to have type
  forall {δ : Type.{u_1}} {π : δ -> Type.{u_2}} [_inst_1 : forall (x : δ), MeasurableSpace.{u_2} (π x)] [_inst_2 : DecidableEq.{succ u_1} δ] {l : List.{u_1} δ} (h : forall (i : δ), Membership.mem.{u_1, u_1} δ (List.{u_1} δ) (List.instMembershipList.{u_1} δ) i l), Measurable.{u_2, max u_1 u_2} (List.TProd.{u_1, u_2} δ π l) (forall (i : δ), π i) (TProd.instMeasurableSpace.{u_1, u_2} δ π (fun (a : δ) => _inst_1 a) l) (MeasurableSpace.pi.{u_1, u_2} δ (fun (i : δ) => π i) (fun (a : δ) => _inst_1 a)) (List.TProd.elim'.{u_1, u_2} δ π l (fun (a : δ) (b : δ) => _inst_2 a b) h)
Case conversion may be inaccurate. Consider using '#align measurable_tprod_elim' measurable_tProd_elim'ₓ'. -/
theorem measurable_tProd_elim' [DecidableEq δ] {l : List δ} (h : ∀ i, i ∈ l) :
    Measurable (TProd.elim' h : TProd π l → ∀ i, π i) :=
  measurable_pi_lambda _ fun i => measurable_tProd_elim (h i)
#align measurable_tprod_elim' measurable_tProd_elim'

/- warning: measurable_set.tprod -> MeasurableSet.tProd is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u_4}} {π : δ -> Type.{u_7}} [_inst_1 : forall (x : δ), MeasurableSpace.{u_7} (π x)] (l : List.{u_4} δ) {s : forall (i : δ), Set.{u_7} (π i)}, (forall (i : δ), MeasurableSet.{u_7} (π i) (_inst_1 i) (s i)) -> (MeasurableSet.{max u_7 u_1} (List.TProd.{u_4, u_7, u_1} δ (fun (i : δ) => π i) l) (TProd.instMeasurableSpace.{u_4, u_7, u_1} δ (fun (i : δ) => π i) (fun (x : δ) => _inst_1 x) l) (Set.tprod.{u_4, u_7, u_1} δ (fun (i : δ) => π i) l s))
but is expected to have type
  forall {δ : Type.{u_1}} {π : δ -> Type.{u_2}} [_inst_1 : forall (x : δ), MeasurableSpace.{u_2} (π x)] (l : List.{u_1} δ) {s : forall (i : δ), Set.{u_2} (π i)}, (forall (i : δ), MeasurableSet.{u_2} (π i) (_inst_1 i) (s i)) -> (MeasurableSet.{u_2} (List.TProd.{u_1, u_2} δ (fun (i : δ) => π i) l) (TProd.instMeasurableSpace.{u_1, u_2} δ (fun (i : δ) => π i) (fun (x : δ) => _inst_1 x) l) (Set.tprod.{u_1, u_2} δ (fun (i : δ) => π i) l s))
Case conversion may be inaccurate. Consider using '#align measurable_set.tprod MeasurableSet.tProdₓ'. -/
theorem MeasurableSet.tProd (l : List δ) {s : ∀ i, Set (π i)} (hs : ∀ i, MeasurableSet (s i)) :
    MeasurableSet (Set.tprod l s) := by
  induction' l with i l ih
  exact MeasurableSet.univ
  exact (hs i).Prod ih
#align measurable_set.tprod MeasurableSet.tProd

end Tprod

instance {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β] : MeasurableSpace (Sum α β) :=
  m₁.map Sum.inl ⊓ m₂.map Sum.inr

section Sum

/- warning: measurable_inl -> measurable_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β], Measurable.{u1, max u1 u2} α (Sum.{u1, u2} α β) _inst_1 (Sum.instMeasurableSpace.{u1, u2} α β _inst_1 _inst_2) (Sum.inl.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β], Measurable.{u2, max u2 u1} α (Sum.{u2, u1} α β) _inst_1 (Sum.instMeasurableSpace.{u2, u1} α β _inst_1 _inst_2) (Sum.inl.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align measurable_inl measurable_inlₓ'. -/
@[measurability]
theorem measurable_inl [MeasurableSpace α] [MeasurableSpace β] : Measurable (@Sum.inl α β) :=
  Measurable.of_le_map inf_le_left
#align measurable_inl measurable_inl

/- warning: measurable_inr -> measurable_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β], Measurable.{u2, max u1 u2} β (Sum.{u1, u2} α β) _inst_2 (Sum.instMeasurableSpace.{u1, u2} α β _inst_1 _inst_2) (Sum.inr.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β], Measurable.{u1, max u2 u1} β (Sum.{u2, u1} α β) _inst_2 (Sum.instMeasurableSpace.{u2, u1} α β _inst_1 _inst_2) (Sum.inr.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align measurable_inr measurable_inrₓ'. -/
@[measurability]
theorem measurable_inr [MeasurableSpace α] [MeasurableSpace β] : Measurable (@Sum.inr α β) :=
  Measurable.of_le_map inf_le_right
#align measurable_inr measurable_inr

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β}

include m mβ

/- warning: measurable_sum -> measurable_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {mγ : MeasurableSpace.{u3} γ} {f : (Sum.{u1, u2} α β) -> γ}, (Measurable.{u1, u3} α γ m mγ (Function.comp.{succ u1, max (succ u1) (succ u2), succ u3} α (Sum.{u1, u2} α β) γ f (Sum.inl.{u1, u2} α β))) -> (Measurable.{u2, u3} β γ mβ mγ (Function.comp.{succ u2, max (succ u1) (succ u2), succ u3} β (Sum.{u1, u2} α β) γ f (Sum.inr.{u1, u2} α β))) -> (Measurable.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.instMeasurableSpace.{u1, u2} α β m mβ) mγ f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} {mγ : MeasurableSpace.{u3} γ} {f : (Sum.{u2, u1} α β) -> γ}, (Measurable.{u2, u3} α γ m mγ (Function.comp.{succ u2, max (succ u2) (succ u1), succ u3} α (Sum.{u2, u1} α β) γ f (Sum.inl.{u2, u1} α β))) -> (Measurable.{u1, u3} β γ mβ mγ (Function.comp.{succ u1, max (succ u2) (succ u1), succ u3} β (Sum.{u2, u1} α β) γ f (Sum.inr.{u2, u1} α β))) -> (Measurable.{max u2 u1, u3} (Sum.{u2, u1} α β) γ (Sum.instMeasurableSpace.{u2, u1} α β m mβ) mγ f)
Case conversion may be inaccurate. Consider using '#align measurable_sum measurable_sumₓ'. -/
theorem measurable_sum {mγ : MeasurableSpace γ} {f : Sum α β → γ} (hl : Measurable (f ∘ Sum.inl))
    (hr : Measurable (f ∘ Sum.inr)) : Measurable f :=
  Measurable.of_comap_le <|
    le_inf (MeasurableSpace.comap_le_iff_le_map.2 <| hl)
      (MeasurableSpace.comap_le_iff_le_map.2 <| hr)
#align measurable_sum measurable_sum

/- warning: measurable.sum_elim -> Measurable.sumElim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {mγ : MeasurableSpace.{u3} γ} {f : α -> γ} {g : β -> γ}, (Measurable.{u1, u3} α γ m mγ f) -> (Measurable.{u2, u3} β γ mβ mγ g) -> (Measurable.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.instMeasurableSpace.{u1, u2} α β m mβ) mγ (Sum.elim.{u1, u2, succ u3} α β γ f g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} {mγ : MeasurableSpace.{u3} γ} {f : α -> γ} {g : β -> γ}, (Measurable.{u2, u3} α γ m mγ f) -> (Measurable.{u1, u3} β γ mβ mγ g) -> (Measurable.{max u1 u2, u3} (Sum.{u2, u1} α β) γ (Sum.instMeasurableSpace.{u2, u1} α β m mβ) mγ (Sum.elim.{u2, u1, succ u3} α β γ f g))
Case conversion may be inaccurate. Consider using '#align measurable.sum_elim Measurable.sumElimₓ'. -/
@[measurability]
theorem Measurable.sumElim {mγ : MeasurableSpace γ} {f : α → γ} {g : β → γ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (Sum.elim f g) :=
  measurable_sum hf hg
#align measurable.sum_elim Measurable.sumElim

/- warning: measurable_set.inl_image -> MeasurableSet.inl_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (MeasurableSet.{max u1 u2} (Sum.{u1, u2} α β) (Sum.instMeasurableSpace.{u1, u2} α β m mβ) (Set.image.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {mβ : MeasurableSpace.{u1} β} {s : Set.{u2} α}, (MeasurableSet.{u2} α m s) -> (MeasurableSet.{max u2 u1} (Sum.{u2, u1} α β) (Sum.instMeasurableSpace.{u2, u1} α β m mβ) (Set.image.{u2, max u2 u1} α (Sum.{u2, u1} α β) (Sum.inl.{u2, u1} α β) s))
Case conversion may be inaccurate. Consider using '#align measurable_set.inl_image MeasurableSet.inl_imageₓ'. -/
theorem MeasurableSet.inl_image {s : Set α} (hs : MeasurableSet s) :
    MeasurableSet (Sum.inl '' s : Set (Sum α β)) :=
  ⟨show MeasurableSet (Sum.inl ⁻¹' _) by
      rwa [preimage_image_eq]
      exact fun a b => Sum.inl.inj,
    have : Sum.inr ⁻¹' (Sum.inl '' s : Set (Sum α β)) = ∅ :=
      eq_empty_of_subset_empty fun x ⟨y, hy, Eq⟩ => by contradiction
    show MeasurableSet (Sum.inr ⁻¹' _) by
      rw [this]
      exact MeasurableSet.empty⟩
#align measurable_set.inl_image MeasurableSet.inl_image

/- warning: measurable_set_inr_image -> measurableSet_inr_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {s : Set.{u2} β}, (MeasurableSet.{u2} β mβ s) -> (MeasurableSet.{max u1 u2} (Sum.{u1, u2} α β) (Sum.instMeasurableSpace.{u1, u2} α β m mβ) (Set.image.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β) s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {mβ : MeasurableSpace.{u2} β} {s : Set.{u2} β}, Iff (MeasurableSet.{max u1 u2} (Sum.{u1, u2} α β) (Sum.instMeasurableSpace.{u1, u2} α β m mβ) (Set.image.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β) s)) (MeasurableSet.{u2} β mβ s)
Case conversion may be inaccurate. Consider using '#align measurable_set_inr_image measurableSet_inr_imageₓ'. -/
theorem measurableSet_inr_image {s : Set β} (hs : MeasurableSet s) :
    MeasurableSet (Sum.inr '' s : Set (Sum α β)) :=
  ⟨have : Sum.inl ⁻¹' (Sum.inr '' s : Set (Sum α β)) = ∅ :=
      eq_empty_of_subset_empty fun x ⟨y, hy, Eq⟩ => by contradiction
    show MeasurableSet (Sum.inl ⁻¹' _) by
      rw [this]
      exact MeasurableSet.empty,
    show MeasurableSet (Sum.inr ⁻¹' _) by
      rwa [preimage_image_eq]
      exact fun a b => Sum.inr.inj⟩
#align measurable_set_inr_image measurableSet_inr_image

omit m

/- warning: measurable_set_range_inl -> measurableSet_range_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {mβ : MeasurableSpace.{u2} β} [_inst_1 : MeasurableSpace.{u1} α], MeasurableSet.{max u1 u2} (Sum.{u1, u2} α β) (Sum.instMeasurableSpace.{u1, u2} α β _inst_1 mβ) (Set.range.{max u1 u2, succ u1} (Sum.{u1, u2} α β) α (Sum.inl.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {mβ : MeasurableSpace.{u1} β} [_inst_1 : MeasurableSpace.{u2} α], MeasurableSet.{max u2 u1} (Sum.{u2, u1} α β) (Sum.instMeasurableSpace.{u2, u1} α β _inst_1 mβ) (Set.range.{max u2 u1, succ u2} (Sum.{u2, u1} α β) α (Sum.inl.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align measurable_set_range_inl measurableSet_range_inlₓ'. -/
theorem measurableSet_range_inl [MeasurableSpace α] :
    MeasurableSet (range Sum.inl : Set (Sum α β)) :=
  by
  rw [← image_univ]
  exact measurable_set.univ.inl_image
#align measurable_set_range_inl measurableSet_range_inl

/- warning: measurable_set_range_inr -> measurableSet_range_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {mβ : MeasurableSpace.{u2} β} [_inst_1 : MeasurableSpace.{u1} α], MeasurableSet.{max u1 u2} (Sum.{u1, u2} α β) (Sum.instMeasurableSpace.{u1, u2} α β _inst_1 mβ) (Set.range.{max u1 u2, succ u2} (Sum.{u1, u2} α β) β (Sum.inr.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {mβ : MeasurableSpace.{u1} β} [_inst_1 : MeasurableSpace.{u2} α], MeasurableSet.{max u2 u1} (Sum.{u2, u1} α β) (Sum.instMeasurableSpace.{u2, u1} α β _inst_1 mβ) (Set.range.{max u2 u1, succ u1} (Sum.{u2, u1} α β) β (Sum.inr.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align measurable_set_range_inr measurableSet_range_inrₓ'. -/
theorem measurableSet_range_inr [MeasurableSpace α] :
    MeasurableSet (range Sum.inr : Set (Sum α β)) :=
  by
  rw [← image_univ]
  exact measurableSet_inr_image MeasurableSet.univ
#align measurable_set_range_inr measurableSet_range_inr

end Sum

instance {α} {β : α → Type _} [m : ∀ a, MeasurableSpace (β a)] : MeasurableSpace (Sigma β) :=
  ⨅ a, (m a).map (Sigma.mk a)

end Constructions

#print MeasurableEmbedding /-
/-- A map `f : α → β` is called a *measurable embedding* if it is injective, measurable, and sends
measurable sets to measurable sets. The latter assumption can be replaced with “`f` has measurable
inverse `g : range f → α`”, see `measurable_embedding.measurable_range_splitting`,
`measurable_embedding.of_measurable_inverse_range`, and
`measurable_embedding.of_measurable_inverse`.

One more interpretation: `f` is a measurable embedding if it defines a measurable equivalence to its
range and the range is a measurable set. One implication is formalized as
`measurable_embedding.equiv_range`; the other one follows from
`measurable_equiv.measurable_embedding`, `measurable_embedding.subtype_coe`, and
`measurable_embedding.comp`. -/
@[protect_proj]
structure MeasurableEmbedding {α β : Type _} [MeasurableSpace α] [MeasurableSpace β] (f : α → β) :
  Prop where
  Injective : Injective f
  Measurable : Measurable f
  measurableSet_image' : ∀ ⦃s⦄, MeasurableSet s → MeasurableSet (f '' s)
#align measurable_embedding MeasurableEmbedding
-/

namespace MeasurableEmbedding

variable {mα : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {g : β → γ}

include mα

/- warning: measurable_embedding.measurable_set_image -> MeasurableEmbedding.measurableSet_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {mα : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β}, (MeasurableEmbedding.{u1, u2} α β mα _inst_1 f) -> (forall {s : Set.{u1} α}, Iff (MeasurableSet.{u2} β _inst_1 (Set.image.{u1, u2} α β f s)) (MeasurableSet.{u1} α mα s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {mα : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β}, (MeasurableEmbedding.{u2, u1} α β mα _inst_1 f) -> (forall {s : Set.{u2} α}, Iff (MeasurableSet.{u1} β _inst_1 (Set.image.{u2, u1} α β f s)) (MeasurableSet.{u2} α mα s))
Case conversion may be inaccurate. Consider using '#align measurable_embedding.measurable_set_image MeasurableEmbedding.measurableSet_imageₓ'. -/
theorem measurableSet_image (hf : MeasurableEmbedding f) {s : Set α} :
    MeasurableSet (f '' s) ↔ MeasurableSet s :=
  ⟨fun h => by simpa only [hf.injective.preimage_image] using hf.measurable h, fun h =>
    hf.measurableSet_image' h⟩
#align measurable_embedding.measurable_set_image MeasurableEmbedding.measurableSet_image

#print MeasurableEmbedding.id /-
theorem id : MeasurableEmbedding (id : α → α) :=
  ⟨injective_id, measurable_id, fun s hs => by rwa [image_id]⟩
#align measurable_embedding.id MeasurableEmbedding.id
-/

/- warning: measurable_embedding.comp -> MeasurableEmbedding.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {mα : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u3} γ] {f : α -> β} {g : β -> γ}, (MeasurableEmbedding.{u2, u3} β γ _inst_1 _inst_2 g) -> (MeasurableEmbedding.{u1, u2} α β mα _inst_1 f) -> (MeasurableEmbedding.{u1, u3} α γ mα _inst_2 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {mα : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u3} β] [_inst_2 : MeasurableSpace.{u2} γ] {f : α -> β} {g : β -> γ}, (MeasurableEmbedding.{u3, u2} β γ _inst_1 _inst_2 g) -> (MeasurableEmbedding.{u1, u3} α β mα _inst_1 f) -> (MeasurableEmbedding.{u1, u2} α γ mα _inst_2 (Function.comp.{succ u1, succ u3, succ u2} α β γ g f))
Case conversion may be inaccurate. Consider using '#align measurable_embedding.comp MeasurableEmbedding.compₓ'. -/
theorem comp (hg : MeasurableEmbedding g) (hf : MeasurableEmbedding f) :
    MeasurableEmbedding (g ∘ f) :=
  ⟨hg.Injective.comp hf.Injective, hg.Measurable.comp hf.Measurable, fun s hs => by
    rwa [← image_image, hg.measurable_set_image, hf.measurable_set_image]⟩
#align measurable_embedding.comp MeasurableEmbedding.comp

#print MeasurableEmbedding.subtype_coe /-
theorem subtype_coe {s : Set α} (hs : MeasurableSet s) : MeasurableEmbedding (coe : s → α) :=
  { Injective := Subtype.coe_injective
    Measurable := measurable_subtype_coe
    measurableSet_image' := fun _ => MeasurableSet.subtype_image hs }
#align measurable_embedding.subtype_coe MeasurableEmbedding.subtype_coe
-/

/- warning: measurable_embedding.measurable_set_range -> MeasurableEmbedding.measurableSet_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {mα : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β}, (MeasurableEmbedding.{u1, u2} α β mα _inst_1 f) -> (MeasurableSet.{u2} β _inst_1 (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {mα : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β}, (MeasurableEmbedding.{u2, u1} α β mα _inst_1 f) -> (MeasurableSet.{u1} β _inst_1 (Set.range.{u1, succ u2} β α f))
Case conversion may be inaccurate. Consider using '#align measurable_embedding.measurable_set_range MeasurableEmbedding.measurableSet_rangeₓ'. -/
theorem measurableSet_range (hf : MeasurableEmbedding f) : MeasurableSet (range f) :=
  by
  rw [← image_univ]
  exact hf.measurable_set_image' MeasurableSet.univ
#align measurable_embedding.measurable_set_range MeasurableEmbedding.measurableSet_range

/- warning: measurable_embedding.measurable_set_preimage -> MeasurableEmbedding.measurableSet_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {mα : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β}, (MeasurableEmbedding.{u1, u2} α β mα _inst_1 f) -> (forall {s : Set.{u2} β}, Iff (MeasurableSet.{u1} α mα (Set.preimage.{u1, u2} α β f s)) (MeasurableSet.{u2} β _inst_1 (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) s (Set.range.{u2, succ u1} β α f))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {mα : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β}, (MeasurableEmbedding.{u2, u1} α β mα _inst_1 f) -> (forall {s : Set.{u1} β}, Iff (MeasurableSet.{u2} α mα (Set.preimage.{u2, u1} α β f s)) (MeasurableSet.{u1} β _inst_1 (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) s (Set.range.{u1, succ u2} β α f))))
Case conversion may be inaccurate. Consider using '#align measurable_embedding.measurable_set_preimage MeasurableEmbedding.measurableSet_preimageₓ'. -/
theorem measurableSet_preimage (hf : MeasurableEmbedding f) {s : Set β} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet (s ∩ range f) := by
  rw [← image_preimage_eq_inter_range, hf.measurable_set_image]
#align measurable_embedding.measurable_set_preimage MeasurableEmbedding.measurableSet_preimage

/- warning: measurable_embedding.measurable_range_splitting -> MeasurableEmbedding.measurable_rangeSplitting is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {mα : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β}, (MeasurableEmbedding.{u1, u2} α β mα _inst_1 f) -> (Measurable.{u2, u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α f)) α (Subtype.instMeasurableSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.range.{u2, succ u1} β α f)) _inst_1) mα (Set.rangeSplitting.{u1, u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {mα : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β}, (MeasurableEmbedding.{u2, u1} α β mα _inst_1 f) -> (Measurable.{u1, u2} (Set.Elem.{u1} β (Set.range.{u1, succ u2} β α f)) α (Subtype.instMeasurableSpace.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.range.{u1, succ u2} β α f)) _inst_1) mα (Set.rangeSplitting.{u2, u1} α β f))
Case conversion may be inaccurate. Consider using '#align measurable_embedding.measurable_range_splitting MeasurableEmbedding.measurable_rangeSplittingₓ'. -/
theorem measurable_rangeSplitting (hf : MeasurableEmbedding f) : Measurable (rangeSplitting f) :=
  fun s hs => by
  rwa [preimage_range_splitting hf.injective, ←
    (subtype_coe hf.measurable_set_range).measurableSet_image, ← image_comp,
    coe_comp_range_factorization, hf.measurable_set_image]
#align measurable_embedding.measurable_range_splitting MeasurableEmbedding.measurable_rangeSplitting

/- warning: measurable_embedding.measurable_extend -> MeasurableEmbedding.measurable_extend is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {mα : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u3} γ] {f : α -> β}, (MeasurableEmbedding.{u1, u2} α β mα _inst_1 f) -> (forall {g : α -> γ} {g' : β -> γ}, (Measurable.{u1, u3} α γ mα _inst_2 g) -> (Measurable.{u2, u3} β γ _inst_1 _inst_2 g') -> (Measurable.{u2, u3} β γ _inst_1 _inst_2 (Function.extend.{succ u1, succ u2, succ u3} α β γ f g g')))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {mα : MeasurableSpace.{u3} α} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u1} γ] {f : α -> β}, (MeasurableEmbedding.{u3, u2} α β mα _inst_1 f) -> (forall {g : α -> γ} {g' : β -> γ}, (Measurable.{u3, u1} α γ mα _inst_2 g) -> (Measurable.{u2, u1} β γ _inst_1 _inst_2 g') -> (Measurable.{u2, u1} β γ _inst_1 _inst_2 (Function.extend.{succ u3, succ u2, succ u1} α β γ f g g')))
Case conversion may be inaccurate. Consider using '#align measurable_embedding.measurable_extend MeasurableEmbedding.measurable_extendₓ'. -/
theorem measurable_extend (hf : MeasurableEmbedding f) {g : α → γ} {g' : β → γ} (hg : Measurable g)
    (hg' : Measurable g') : Measurable (extend f g g') :=
  by
  refine' measurable_of_restrict_of_restrict_compl hf.measurable_set_range _ _
  · rw [restrict_extend_range]
    simpa only [range_splitting] using hg.comp hf.measurable_range_splitting
  · rw [restrict_extend_compl_range]
    exact hg'.comp measurable_subtype_coe
#align measurable_embedding.measurable_extend MeasurableEmbedding.measurable_extend

/- warning: measurable_embedding.exists_measurable_extend -> MeasurableEmbedding.exists_measurable_extend is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {mα : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u3} γ] {f : α -> β}, (MeasurableEmbedding.{u1, u2} α β mα _inst_1 f) -> (forall {g : α -> γ}, (Measurable.{u1, u3} α γ mα _inst_2 g) -> (β -> (Nonempty.{succ u3} γ)) -> (Exists.{max (succ u2) (succ u3)} (β -> γ) (fun (g' : β -> γ) => And (Measurable.{u2, u3} β γ _inst_1 _inst_2 g') (Eq.{max (succ u1) (succ u3)} (α -> γ) (Function.comp.{succ u1, succ u2, succ u3} α β γ g' f) g))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {mα : MeasurableSpace.{u3} α} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u1} γ] {f : α -> β}, (MeasurableEmbedding.{u3, u2} α β mα _inst_1 f) -> (forall {g : α -> γ}, (Measurable.{u3, u1} α γ mα _inst_2 g) -> (β -> (Nonempty.{succ u1} γ)) -> (Exists.{max (succ u2) (succ u1)} (β -> γ) (fun (g' : β -> γ) => And (Measurable.{u2, u1} β γ _inst_1 _inst_2 g') (Eq.{max (succ u3) (succ u1)} (α -> γ) (Function.comp.{succ u3, succ u2, succ u1} α β γ g' f) g))))
Case conversion may be inaccurate. Consider using '#align measurable_embedding.exists_measurable_extend MeasurableEmbedding.exists_measurable_extendₓ'. -/
theorem exists_measurable_extend (hf : MeasurableEmbedding f) {g : α → γ} (hg : Measurable g)
    (hne : β → Nonempty γ) : ∃ g' : β → γ, Measurable g' ∧ g' ∘ f = g :=
  ⟨extend f g fun x => Classical.choice (hne x),
    hf.measurable_extend hg (measurable_const' fun _ _ => rfl),
    funext fun x => hf.Injective.extend_apply _ _ _⟩
#align measurable_embedding.exists_measurable_extend MeasurableEmbedding.exists_measurable_extend

/- warning: measurable_embedding.measurable_comp_iff -> MeasurableEmbedding.measurable_comp_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {mα : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u3} γ] {f : α -> β} {g : β -> γ}, (MeasurableEmbedding.{u2, u3} β γ _inst_1 _inst_2 g) -> (Iff (Measurable.{u1, u3} α γ mα _inst_2 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)) (Measurable.{u1, u2} α β mα _inst_1 f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {mα : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u3} β] [_inst_2 : MeasurableSpace.{u2} γ] {f : α -> β} {g : β -> γ}, (MeasurableEmbedding.{u3, u2} β γ _inst_1 _inst_2 g) -> (Iff (Measurable.{u1, u2} α γ mα _inst_2 (Function.comp.{succ u1, succ u3, succ u2} α β γ g f)) (Measurable.{u1, u3} α β mα _inst_1 f))
Case conversion may be inaccurate. Consider using '#align measurable_embedding.measurable_comp_iff MeasurableEmbedding.measurable_comp_iffₓ'. -/
theorem measurable_comp_iff (hg : MeasurableEmbedding g) : Measurable (g ∘ f) ↔ Measurable f :=
  by
  refine' ⟨fun H => _, hg.measurable.comp⟩
  suffices Measurable ((range_splitting g ∘ range_factorization g) ∘ f) by
    rwa [(right_inverse_range_splitting hg.injective).comp_eq_id] at this
  exact hg.measurable_range_splitting.comp H.subtype_mk
#align measurable_embedding.measurable_comp_iff MeasurableEmbedding.measurable_comp_iff

end MeasurableEmbedding

#print MeasurableSet.exists_measurable_proj /-
theorem MeasurableSet.exists_measurable_proj {m : MeasurableSpace α} {s : Set α}
    (hs : MeasurableSet s) (hne : s.Nonempty) : ∃ f : α → s, Measurable f ∧ ∀ x : s, f x = x :=
  let ⟨f, hfm, hf⟩ :=
    (MeasurableEmbedding.subtype_coe hs).exists_measurable_extend measurable_id fun _ =>
      hne.to_subtype
  ⟨f, hfm, congr_fun hf⟩
#align measurable_set.exists_measurable_proj MeasurableSet.exists_measurable_proj
-/

#print MeasurableEquiv /-
/-- Equivalences between measurable spaces. Main application is the simplification of measurability
statements along measurable equivalences. -/
structure MeasurableEquiv (α β : Type _) [MeasurableSpace α] [MeasurableSpace β] extends α ≃ β where
  measurable_to_fun : Measurable to_equiv
  measurable_inv_fun : Measurable to_equiv.symm
#align measurable_equiv MeasurableEquiv
-/

-- mathport name: «expr ≃ᵐ »
infixl:25 " ≃ᵐ " => MeasurableEquiv

namespace MeasurableEquiv

variable (α β) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

instance : CoeFun (α ≃ᵐ β) fun _ => α → β :=
  ⟨fun e => e.toFun⟩

variable {α β}

/- warning: measurable_equiv.coe_to_equiv -> MeasurableEquiv.coe_toEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} ((fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (MeasurableEquiv.toEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) (MeasurableEquiv.toEquiv.{u1, u2} α β _inst_1 _inst_2 e)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) (MeasurableEquiv.toEquiv.{u2, u1} α β _inst_1 _inst_2 e)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.coe_to_equiv MeasurableEquiv.coe_toEquivₓ'. -/
@[simp]
theorem coe_toEquiv (e : α ≃ᵐ β) : (e.toEquiv : α → β) = e :=
  rfl
#align measurable_equiv.coe_to_equiv MeasurableEquiv.coe_toEquiv

/- warning: measurable_equiv.measurable -> MeasurableEquiv.measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2), Measurable.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2), Measurable.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.measurable MeasurableEquiv.measurableₓ'. -/
@[measurability]
protected theorem measurable (e : α ≃ᵐ β) : Measurable (e : α → β) :=
  e.measurable_to_fun
#align measurable_equiv.measurable MeasurableEquiv.measurable

/- warning: measurable_equiv.coe_mk -> MeasurableEquiv.coe_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : Equiv.{succ u1, succ u2} α β) (h1 : Measurable.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e)) (h2 : Measurable.{u2, u1} β α _inst_2 _inst_1 (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β e))), Eq.{max (succ u1) (succ u2)} ((fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.mk.{u1, u2} α β _inst_1 _inst_2 e h1 h2)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (MeasurableEquiv.mk.{u1, u2} α β _inst_1 _inst_2 e h1 h2)) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : Equiv.{succ u2, succ u1} α β) (h1 : Measurable.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) e)) (h2 : Measurable.{u1, u2} β α _inst_2 _inst_1 (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β e))), Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) (MeasurableEquiv.mk.{u2, u1} α β _inst_1 _inst_2 e h1 h2)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) e)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.coe_mk MeasurableEquiv.coe_mkₓ'. -/
@[simp]
theorem coe_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) :
    ((⟨e, h1, h2⟩ : α ≃ᵐ β) : α → β) = e :=
  rfl
#align measurable_equiv.coe_mk MeasurableEquiv.coe_mk

#print MeasurableEquiv.refl /-
/-- Any measurable space is equivalent to itself. -/
def refl (α : Type _) [MeasurableSpace α] : α ≃ᵐ α
    where
  toEquiv := Equiv.refl α
  measurable_to_fun := measurable_id
  measurable_inv_fun := measurable_id
#align measurable_equiv.refl MeasurableEquiv.refl
-/

instance : Inhabited (α ≃ᵐ α) :=
  ⟨refl α⟩

#print MeasurableEquiv.trans /-
/-- The composition of equivalences between measurable spaces. -/
def trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : α ≃ᵐ γ
    where
  toEquiv := ab.toEquiv.trans bc.toEquiv
  measurable_to_fun := bc.measurable_to_fun.comp ab.measurable_to_fun
  measurable_inv_fun := ab.measurable_inv_fun.comp bc.measurable_inv_fun
#align measurable_equiv.trans MeasurableEquiv.trans
-/

#print MeasurableEquiv.symm /-
/-- The inverse of an equivalence between measurable spaces. -/
def symm (ab : α ≃ᵐ β) : β ≃ᵐ α where
  toEquiv := ab.toEquiv.symm
  measurable_to_fun := ab.measurable_inv_fun
  measurable_inv_fun := ab.measurable_to_fun
#align measurable_equiv.symm MeasurableEquiv.symm
-/

/- warning: measurable_equiv.coe_to_equiv_symm -> MeasurableEquiv.coe_toEquiv_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} ((fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.symm.{succ u1, succ u2} α β (MeasurableEquiv.toEquiv.{u1, u2} α β _inst_1 _inst_2 e))) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β (MeasurableEquiv.toEquiv.{u1, u2} α β _inst_1 _inst_2 e))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (MeasurableEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (MeasurableEquiv.symm.{u1, u2} α β _inst_1 _inst_2 e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (forall (a : β), (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : β) => α) a) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β (MeasurableEquiv.toEquiv.{u2, u1} α β _inst_1 _inst_2 e))) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (MeasurableEquiv.instEquivLike.{u1, u2} β α _inst_2 _inst_1))) (MeasurableEquiv.symm.{u2, u1} α β _inst_1 _inst_2 e))
Case conversion may be inaccurate. Consider using '#align measurable_equiv.coe_to_equiv_symm MeasurableEquiv.coe_toEquiv_symmₓ'. -/
@[simp]
theorem coe_toEquiv_symm (e : α ≃ᵐ β) : (e.toEquiv.symm : β → α) = e.symm :=
  rfl
#align measurable_equiv.coe_to_equiv_symm MeasurableEquiv.coe_toEquiv_symm

#print MeasurableEquiv.Simps.apply /-
/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : α ≃ᵐ β) : α → β :=
  h
#align measurable_equiv.simps.apply MeasurableEquiv.Simps.apply
-/

#print MeasurableEquiv.Simps.symm_apply /-
/-- See Note [custom simps projection] -/
def Simps.symm_apply (h : α ≃ᵐ β) : β → α :=
  h.symm
#align measurable_equiv.simps.symm_apply MeasurableEquiv.Simps.symm_apply
-/

initialize_simps_projections MeasurableEquiv (to_equiv_to_fun → apply, to_equiv_inv_fun →
  symm_apply)

/- warning: measurable_equiv.to_equiv_injective -> MeasurableEquiv.toEquiv_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β], Function.Injective.{max (succ u1) (succ u2), max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (Equiv.{succ u1, succ u2} α β) (MeasurableEquiv.toEquiv.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) (Equiv.{succ u2, succ u1} α β) (MeasurableEquiv.toEquiv.{u2, u1} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.to_equiv_injective MeasurableEquiv.toEquiv_injectiveₓ'. -/
theorem toEquiv_injective : Injective (toEquiv : α ≃ᵐ β → α ≃ β) :=
  by
  rintro ⟨e₁, _, _⟩ ⟨e₂, _, _⟩ (rfl : e₁ = e₂)
  rfl
#align measurable_equiv.to_equiv_injective MeasurableEquiv.toEquiv_injective

/- warning: measurable_equiv.ext -> MeasurableEquiv.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {e₁ : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2} {e₂ : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2}, (Eq.{max (succ u1) (succ u2)} ((fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) e₁) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e₁) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e₂)) -> (Eq.{max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) e₁ e₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {e₁ : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2} {e₂ : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2}, (Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e₁) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e₂)) -> (Eq.{max (succ u2) (succ u1)} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) e₁ e₂)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.ext MeasurableEquiv.extₓ'. -/
@[ext]
theorem ext {e₁ e₂ : α ≃ᵐ β} (h : (e₁ : α → β) = e₂) : e₁ = e₂ :=
  toEquiv_injective <| Equiv.coe_fn_injective h
#align measurable_equiv.ext MeasurableEquiv.ext

/- warning: measurable_equiv.symm_mk -> MeasurableEquiv.symm_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : Equiv.{succ u1, succ u2} α β) (h1 : Measurable.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e)) (h2 : Measurable.{u2, u1} β α _inst_2 _inst_1 (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β e))), Eq.{max (succ u2) (succ u1)} (MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) (MeasurableEquiv.symm.{u1, u2} α β _inst_1 _inst_2 (MeasurableEquiv.mk.{u1, u2} α β _inst_1 _inst_2 e h1 h2)) (MeasurableEquiv.mk.{u2, u1} β α _inst_2 _inst_1 (Equiv.symm.{succ u1, succ u2} α β e) h2 h1)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : Equiv.{succ u2, succ u1} α β) (h1 : Measurable.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) e)) (h2 : Measurable.{u1, u2} β α _inst_2 _inst_1 (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β e))), Eq.{max (succ u2) (succ u1)} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) (MeasurableEquiv.symm.{u2, u1} α β _inst_1 _inst_2 (MeasurableEquiv.mk.{u2, u1} α β _inst_1 _inst_2 e h1 h2)) (MeasurableEquiv.mk.{u1, u2} β α _inst_2 _inst_1 (Equiv.symm.{succ u2, succ u1} α β e) h2 h1)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.symm_mk MeasurableEquiv.symm_mkₓ'. -/
@[simp]
theorem symm_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) :
    (⟨e, h1, h2⟩ : α ≃ᵐ β).symm = ⟨e.symm, h2, h1⟩ :=
  rfl
#align measurable_equiv.symm_mk MeasurableEquiv.symm_mk

attribute [simps apply toEquiv] trans refl

#print MeasurableEquiv.symm_refl /-
@[simp]
theorem symm_refl (α : Type _) [MeasurableSpace α] : (refl α).symm = refl α :=
  rfl
#align measurable_equiv.symm_refl MeasurableEquiv.symm_refl
-/

/- warning: measurable_equiv.symm_comp_self -> MeasurableEquiv.symm_comp_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u1} (α -> α) (Function.comp.{succ u1, succ u2, succ u1} α β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (MeasurableEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (MeasurableEquiv.symm.{u1, u2} α β _inst_1 _inst_2 e)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)) (id.{succ u1} α)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u2} (α -> α) (Function.comp.{succ u2, succ u1, succ u2} α β α (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (MeasurableEquiv.instEquivLike.{u1, u2} β α _inst_2 _inst_1))) (MeasurableEquiv.symm.{u2, u1} α β _inst_1 _inst_2 e)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e)) (id.{succ u2} α)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.symm_comp_self MeasurableEquiv.symm_comp_selfₓ'. -/
@[simp]
theorem symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e = id :=
  funext e.left_inv
#align measurable_equiv.symm_comp_self MeasurableEquiv.symm_comp_self

/- warning: measurable_equiv.self_comp_symm -> MeasurableEquiv.self_comp_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u2} (β -> β) (Function.comp.{succ u2, succ u1, succ u2} β α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (MeasurableEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (MeasurableEquiv.symm.{u1, u2} α β _inst_1 _inst_2 e))) (id.{succ u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u1} (β -> β) (Function.comp.{succ u1, succ u2, succ u1} β α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (MeasurableEquiv.instEquivLike.{u1, u2} β α _inst_2 _inst_1))) (MeasurableEquiv.symm.{u2, u1} α β _inst_1 _inst_2 e))) (id.{succ u1} β)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.self_comp_symm MeasurableEquiv.self_comp_symmₓ'. -/
@[simp]
theorem self_comp_symm (e : α ≃ᵐ β) : e ∘ e.symm = id :=
  funext e.right_inv
#align measurable_equiv.self_comp_symm MeasurableEquiv.self_comp_symm

/- warning: measurable_equiv.apply_symm_apply -> MeasurableEquiv.apply_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (y : β), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (MeasurableEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (MeasurableEquiv.symm.{u1, u2} α β _inst_1 _inst_2 e) y)) y
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) (y : β), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (MeasurableEquiv.instEquivLike.{u1, u2} β α _inst_2 _inst_1))) (MeasurableEquiv.symm.{u2, u1} α β _inst_1 _inst_2 e) y)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (MeasurableEquiv.instEquivLike.{u1, u2} β α _inst_2 _inst_1))) (MeasurableEquiv.symm.{u2, u1} α β _inst_1 _inst_2 e) y)) y
Case conversion may be inaccurate. Consider using '#align measurable_equiv.apply_symm_apply MeasurableEquiv.apply_symm_applyₓ'. -/
@[simp]
theorem apply_symm_apply (e : α ≃ᵐ β) (y : β) : e (e.symm y) = y :=
  e.right_inv y
#align measurable_equiv.apply_symm_apply MeasurableEquiv.apply_symm_apply

/- warning: measurable_equiv.symm_apply_apply -> MeasurableEquiv.symm_apply_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (x : α), Eq.{succ u1} α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (MeasurableEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (MeasurableEquiv.symm.{u1, u2} α β _inst_1 _inst_2 e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e x)) x
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e x)) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (MeasurableEquiv.instEquivLike.{u1, u2} β α _inst_2 _inst_1))) (MeasurableEquiv.symm.{u2, u1} α β _inst_1 _inst_2 e) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e x)) x
Case conversion may be inaccurate. Consider using '#align measurable_equiv.symm_apply_apply MeasurableEquiv.symm_apply_applyₓ'. -/
@[simp]
theorem symm_apply_apply (e : α ≃ᵐ β) (x : α) : e.symm (e x) = x :=
  e.left_inv x
#align measurable_equiv.symm_apply_apply MeasurableEquiv.symm_apply_apply

/- warning: measurable_equiv.symm_trans_self -> MeasurableEquiv.symm_trans_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u2} (MeasurableEquiv.{u2, u2} β β _inst_2 _inst_2) (MeasurableEquiv.trans.{u2, u1, u2} β α β _inst_2 _inst_1 _inst_2 (MeasurableEquiv.symm.{u1, u2} α β _inst_1 _inst_2 e) e) (MeasurableEquiv.refl.{u2} β _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u1} (MeasurableEquiv.{u1, u1} β β _inst_2 _inst_2) (MeasurableEquiv.trans.{u1, u2, u1} β α β _inst_2 _inst_1 _inst_2 (MeasurableEquiv.symm.{u2, u1} α β _inst_1 _inst_2 e) e) (MeasurableEquiv.refl.{u1} β _inst_2)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.symm_trans_self MeasurableEquiv.symm_trans_selfₓ'. -/
@[simp]
theorem symm_trans_self (e : α ≃ᵐ β) : e.symm.trans e = refl β :=
  ext e.self_comp_symm
#align measurable_equiv.symm_trans_self MeasurableEquiv.symm_trans_self

/- warning: measurable_equiv.self_trans_symm -> MeasurableEquiv.self_trans_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u1} (MeasurableEquiv.{u1, u1} α α _inst_1 _inst_1) (MeasurableEquiv.trans.{u1, u2, u1} α β α _inst_1 _inst_2 _inst_1 e (MeasurableEquiv.symm.{u1, u2} α β _inst_1 _inst_2 e)) (MeasurableEquiv.refl.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u2} (MeasurableEquiv.{u2, u2} α α _inst_1 _inst_1) (MeasurableEquiv.trans.{u2, u1, u2} α β α _inst_1 _inst_2 _inst_1 e (MeasurableEquiv.symm.{u2, u1} α β _inst_1 _inst_2 e)) (MeasurableEquiv.refl.{u2} α _inst_1)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.self_trans_symm MeasurableEquiv.self_trans_symmₓ'. -/
@[simp]
theorem self_trans_symm (e : α ≃ᵐ β) : e.trans e.symm = refl α :=
  ext e.symm_comp_self
#align measurable_equiv.self_trans_symm MeasurableEquiv.self_trans_symm

/- warning: measurable_equiv.surjective -> MeasurableEquiv.surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2), Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2), Function.Surjective.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.surjective MeasurableEquiv.surjectiveₓ'. -/
protected theorem surjective (e : α ≃ᵐ β) : Surjective e :=
  e.toEquiv.Surjective
#align measurable_equiv.surjective MeasurableEquiv.surjective

/- warning: measurable_equiv.bijective -> MeasurableEquiv.bijective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2), Function.Bijective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2), Function.Bijective.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.bijective MeasurableEquiv.bijectiveₓ'. -/
protected theorem bijective (e : α ≃ᵐ β) : Bijective e :=
  e.toEquiv.Bijective
#align measurable_equiv.bijective MeasurableEquiv.bijective

/- warning: measurable_equiv.injective -> MeasurableEquiv.injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2), Function.Injective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2), Function.Injective.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.injective MeasurableEquiv.injectiveₓ'. -/
protected theorem injective (e : α ≃ᵐ β) : Injective e :=
  e.toEquiv.Injective
#align measurable_equiv.injective MeasurableEquiv.injective

/- warning: measurable_equiv.symm_preimage_preimage -> MeasurableEquiv.symm_preimage_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (MeasurableEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (MeasurableEquiv.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s)) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Set.preimage.{u1, u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (MeasurableEquiv.instEquivLike.{u1, u2} β α _inst_2 _inst_1))) (MeasurableEquiv.symm.{u2, u1} α β _inst_1 _inst_2 e)) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e) s)) s
Case conversion may be inaccurate. Consider using '#align measurable_equiv.symm_preimage_preimage MeasurableEquiv.symm_preimage_preimageₓ'. -/
@[simp]
theorem symm_preimage_preimage (e : α ≃ᵐ β) (s : Set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.toEquiv.symm_preimage_preimage s
#align measurable_equiv.symm_preimage_preimage MeasurableEquiv.symm_preimage_preimage

/- warning: measurable_equiv.image_eq_preimage -> MeasurableEquiv.image_eq_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (MeasurableEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (MeasurableEquiv.symm.{u1, u2} α β _inst_1 _inst_2 e)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e) s) (Set.preimage.{u1, u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (MeasurableEquiv.instEquivLike.{u1, u2} β α _inst_2 _inst_1))) (MeasurableEquiv.symm.{u2, u1} α β _inst_1 _inst_2 e)) s)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.image_eq_preimage MeasurableEquiv.image_eq_preimageₓ'. -/
theorem image_eq_preimage (e : α ≃ᵐ β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s
#align measurable_equiv.image_eq_preimage MeasurableEquiv.image_eq_preimage

/- warning: measurable_equiv.measurable_set_preimage -> MeasurableEquiv.measurableSet_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u2} β}, Iff (MeasurableSet.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s)) (MeasurableSet.{u2} β _inst_2 s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) {s : Set.{u1} β}, Iff (MeasurableSet.{u2} α _inst_1 (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e) s)) (MeasurableSet.{u1} β _inst_2 s)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.measurable_set_preimage MeasurableEquiv.measurableSet_preimageₓ'. -/
@[simp]
theorem measurableSet_preimage (e : α ≃ᵐ β) {s : Set β} :
    MeasurableSet (e ⁻¹' s) ↔ MeasurableSet s :=
  ⟨fun h => by simpa only [symm_preimage_preimage] using e.symm.measurable h, fun h =>
    e.Measurable h⟩
#align measurable_equiv.measurable_set_preimage MeasurableEquiv.measurableSet_preimage

/- warning: measurable_equiv.measurable_set_image -> MeasurableEquiv.measurableSet_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u1} α}, Iff (MeasurableSet.{u2} β _inst_2 (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s)) (MeasurableSet.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) {s : Set.{u2} α}, Iff (MeasurableSet.{u1} β _inst_2 (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e) s)) (MeasurableSet.{u2} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.measurable_set_image MeasurableEquiv.measurableSet_imageₓ'. -/
@[simp]
theorem measurableSet_image (e : α ≃ᵐ β) {s : Set α} : MeasurableSet (e '' s) ↔ MeasurableSet s :=
  by rw [image_eq_preimage, measurableSet_preimage]
#align measurable_equiv.measurable_set_image MeasurableEquiv.measurableSet_image

/- warning: measurable_equiv.measurable_embedding -> MeasurableEquiv.measurableEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2), MeasurableEmbedding.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2), MeasurableEmbedding.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.measurable_embedding MeasurableEquiv.measurableEmbeddingₓ'. -/
/-- A measurable equivalence is a measurable embedding. -/
protected theorem measurableEmbedding (e : α ≃ᵐ β) : MeasurableEmbedding e :=
  { Injective := e.Injective
    Measurable := e.Measurable
    measurableSet_image' := fun s => e.measurableSet_image.2 }
#align measurable_equiv.measurable_embedding MeasurableEquiv.measurableEmbedding

#print MeasurableEquiv.cast /-
/-- Equal measurable spaces are equivalent. -/
protected def cast {α β} [i₁ : MeasurableSpace α] [i₂ : MeasurableSpace β] (h : α = β)
    (hi : HEq i₁ i₂) : α ≃ᵐ β where
  toEquiv := Equiv.cast h
  measurable_to_fun := by
    subst h
    subst hi
    exact measurable_id
  measurable_inv_fun := by
    subst h
    subst hi
    exact measurable_id
#align measurable_equiv.cast MeasurableEquiv.cast
-/

/- warning: measurable_equiv.measurable_comp_iff -> MeasurableEquiv.measurable_comp_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : MeasurableSpace.{u3} γ] {f : β -> γ} (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2), Iff (Measurable.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e))) (Measurable.{u2, u3} β γ _inst_2 _inst_3 f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : MeasurableSpace.{u1} γ] {f : β -> γ} (e : MeasurableEquiv.{u3, u2} α β _inst_1 _inst_2), Iff (Measurable.{u3, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} α β γ f (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MeasurableEquiv.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (MeasurableEquiv.{u3, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (MeasurableEquiv.{u3, u2} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u3, u2} α β _inst_1 _inst_2))) e))) (Measurable.{u2, u1} β γ _inst_2 _inst_3 f)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.measurable_comp_iff MeasurableEquiv.measurable_comp_iffₓ'. -/
protected theorem measurable_comp_iff {f : β → γ} (e : α ≃ᵐ β) :
    Measurable (f ∘ e) ↔ Measurable f :=
  Iff.intro
    (fun hfe =>
      by
      have : Measurable (f ∘ (e.symm.trans e).toEquiv) := hfe.comp e.symm.Measurable
      rwa [coe_to_equiv, symm_trans_self] at this)
    fun h => h.comp e.Measurable
#align measurable_equiv.measurable_comp_iff MeasurableEquiv.measurable_comp_iff

#print MeasurableEquiv.ofUniqueOfUnique /-
/-- Any two types with unique elements are measurably equivalent. -/
def ofUniqueOfUnique (α β : Type _) [MeasurableSpace α] [MeasurableSpace β] [Unique α] [Unique β] :
    α ≃ᵐ β where
  toEquiv := equivOfUnique α β
  measurable_to_fun := Subsingleton.measurable
  measurable_inv_fun := Subsingleton.measurable
#align measurable_equiv.of_unique_of_unique MeasurableEquiv.ofUniqueOfUnique
-/

#print MeasurableEquiv.prodCongr /-
/-- Products of equivalent measurable spaces are equivalent. -/
def prodCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α × γ ≃ᵐ β × δ
    where
  toEquiv := prodCongr ab.toEquiv cd.toEquiv
  measurable_to_fun :=
    (ab.measurable_to_fun.comp measurable_id.fst).prod_mk
      (cd.measurable_to_fun.comp measurable_id.snd)
  measurable_inv_fun :=
    (ab.measurable_inv_fun.comp measurable_id.fst).prod_mk
      (cd.measurable_inv_fun.comp measurable_id.snd)
#align measurable_equiv.prod_congr MeasurableEquiv.prodCongr
-/

#print MeasurableEquiv.prodComm /-
/-- Products of measurable spaces are symmetric. -/
def prodComm : α × β ≃ᵐ β × α where
  toEquiv := prodComm α β
  measurable_to_fun := measurable_id.snd.prod_mk measurable_id.fst
  measurable_inv_fun := measurable_id.snd.prod_mk measurable_id.fst
#align measurable_equiv.prod_comm MeasurableEquiv.prodComm
-/

#print MeasurableEquiv.prodAssoc /-
/-- Products of measurable spaces are associative. -/
def prodAssoc : (α × β) × γ ≃ᵐ α × β × γ
    where
  toEquiv := prodAssoc α β γ
  measurable_to_fun := measurable_fst.fst.prod_mk <| measurable_fst.snd.prod_mk measurable_snd
  measurable_inv_fun := (measurable_fst.prod_mk measurable_snd.fst).prod_mk measurable_snd.snd
#align measurable_equiv.prod_assoc MeasurableEquiv.prodAssoc
-/

#print MeasurableEquiv.sumCongr /-
/-- Sums of measurable spaces are symmetric. -/
def sumCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : Sum α γ ≃ᵐ Sum β δ
    where
  toEquiv := sumCongr ab.toEquiv cd.toEquiv
  measurable_to_fun := by
    cases' ab with ab' abm; cases ab'; cases' cd with cd' cdm; cases cd'
    refine' measurable_sum (measurable_inl.comp abm) (measurable_inr.comp cdm)
  measurable_inv_fun := by
    cases' ab with ab' _ abm; cases ab'; cases' cd with cd' _ cdm; cases cd'
    refine' measurable_sum (measurable_inl.comp abm) (measurable_inr.comp cdm)
#align measurable_equiv.sum_congr MeasurableEquiv.sumCongr
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print MeasurableEquiv.Set.prod /-
/-- `s ×ˢ t ≃ (s × t)` as measurable spaces. -/
def Set.prod (s : Set α) (t : Set β) : ↥(s ×ˢ t) ≃ᵐ s × t
    where
  toEquiv := Equiv.Set.prod s t
  measurable_to_fun :=
    measurable_id.subtype_val.fst.subtype_mk.prod_mk measurable_id.subtype_val.snd.subtype_mk
  measurable_inv_fun :=
    Measurable.subtype_mk <| measurable_id.fst.subtype_val.prod_mk measurable_id.snd.subtype_val
#align measurable_equiv.set.prod MeasurableEquiv.Set.prod
-/

#print MeasurableEquiv.Set.univ /-
/-- `univ α ≃ α` as measurable spaces. -/
def Set.univ (α : Type _) [MeasurableSpace α] : (univ : Set α) ≃ᵐ α
    where
  toEquiv := Equiv.Set.univ α
  measurable_to_fun := measurable_id.subtype_val
  measurable_inv_fun := measurable_id.subtype_mk
#align measurable_equiv.set.univ MeasurableEquiv.Set.univ
-/

#print MeasurableEquiv.Set.singleton /-
/-- `{a} ≃ unit` as measurable spaces. -/
def Set.singleton (a : α) : ({a} : Set α) ≃ᵐ Unit
    where
  toEquiv := Equiv.Set.singleton a
  measurable_to_fun := measurable_const
  measurable_inv_fun := measurable_const
#align measurable_equiv.set.singleton MeasurableEquiv.Set.singleton
-/

#print MeasurableEquiv.Set.rangeInl /-
/-- `α` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
def Set.rangeInl : (range Sum.inl : Set (Sum α β)) ≃ᵐ α
    where
  toFun ab :=
    match ab with
    | ⟨Sum.inl a, _⟩ => a
    | ⟨Sum.inr b, p⟩ =>
      have : False := by
        cases p
        contradiction
      this.elim
  invFun a := ⟨Sum.inl a, a, rfl⟩
  left_inv := by
    rintro ⟨ab, a, rfl⟩
    rfl
  right_inv a := rfl
  measurable_to_fun s (hs : MeasurableSet s) :=
    by
    refine' ⟨_, hs.inl_image, Set.ext _⟩
    rintro ⟨ab, a, rfl⟩
    simp [set.range_inl._match_1]
  measurable_inv_fun := Measurable.subtype_mk measurable_inl
#align measurable_equiv.set.range_inl MeasurableEquiv.Set.rangeInl
-/

#print MeasurableEquiv.Set.rangeInr /-
/-- `β` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
def Set.rangeInr : (range Sum.inr : Set (Sum α β)) ≃ᵐ β
    where
  toFun ab :=
    match ab with
    | ⟨Sum.inr b, _⟩ => b
    | ⟨Sum.inl a, p⟩ =>
      have : False := by
        cases p
        contradiction
      this.elim
  invFun b := ⟨Sum.inr b, b, rfl⟩
  left_inv := by
    rintro ⟨ab, b, rfl⟩
    rfl
  right_inv b := rfl
  measurable_to_fun s (hs : MeasurableSet s) :=
    by
    refine' ⟨_, measurableSet_inr_image hs, Set.ext _⟩
    rintro ⟨ab, b, rfl⟩
    simp [set.range_inr._match_1]
  measurable_inv_fun := Measurable.subtype_mk measurable_inr
#align measurable_equiv.set.range_inr MeasurableEquiv.Set.rangeInr
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print MeasurableEquiv.sumProdDistrib /-
/-- Products distribute over sums (on the right) as measurable spaces. -/
def sumProdDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    Sum α β × γ ≃ᵐ Sum (α × γ) (β × γ)
    where
  toEquiv := sumProdDistrib α β γ
  measurable_to_fun :=
    by
    refine'
      measurable_of_measurable_union_cover (range Sum.inl ×ˢ (univ : Set γ))
        (range Sum.inr ×ˢ (univ : Set γ)) (measurable_set_range_inl.prod MeasurableSet.univ)
        (measurable_set_range_inr.prod MeasurableSet.univ)
        (by rintro ⟨a | b, c⟩ <;> simp [Set.prod_eq]) _ _
    · refine' (Set.prod (range Sum.inl) univ).symm.measurable_comp_iff.1 _
      refine' (prod_congr Set.range_inl (Set.univ _)).symm.measurable_comp_iff.1 _
      dsimp [(· ∘ ·)]
      convert measurable_inl
      ext ⟨a, c⟩
      rfl
    · refine' (Set.prod (range Sum.inr) univ).symm.measurable_comp_iff.1 _
      refine' (prod_congr Set.range_inr (Set.univ _)).symm.measurable_comp_iff.1 _
      dsimp [(· ∘ ·)]
      convert measurable_inr
      ext ⟨b, c⟩
      rfl
  measurable_inv_fun :=
    measurable_sum ((measurable_inl.comp measurable_fst).prod_mk measurable_snd)
      ((measurable_inr.comp measurable_fst).prod_mk measurable_snd)
#align measurable_equiv.sum_prod_distrib MeasurableEquiv.sumProdDistrib
-/

#print MeasurableEquiv.prodSumDistrib /-
/-- Products distribute over sums (on the left) as measurable spaces. -/
def prodSumDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    α × Sum β γ ≃ᵐ Sum (α × β) (α × γ) :=
  prodComm.trans <| (sumProdDistrib _ _ _).trans <| sumCongr prodComm prodComm
#align measurable_equiv.prod_sum_distrib MeasurableEquiv.prodSumDistrib
-/

#print MeasurableEquiv.sumProdSum /-
/-- Products distribute over sums as measurable spaces. -/
def sumProdSum (α β γ δ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] : Sum α β × Sum γ δ ≃ᵐ Sum (Sum (α × γ) (α × δ)) (Sum (β × γ) (β × δ)) :=
  (sumProdDistrib _ _ _).trans <| sumCongr (prodSumDistrib _ _ _) (prodSumDistrib _ _ _)
#align measurable_equiv.sum_prod_sum MeasurableEquiv.sumProdSum
-/

variable {π π' : δ' → Type _} [∀ x, MeasurableSpace (π x)] [∀ x, MeasurableSpace (π' x)]

#print MeasurableEquiv.piCongrRight /-
/-- A family of measurable equivalences `Π a, β₁ a ≃ᵐ β₂ a` generates a measurable equivalence
  between  `Π a, β₁ a` and `Π a, β₂ a`. -/
def piCongrRight (e : ∀ a, π a ≃ᵐ π' a) : (∀ a, π a) ≃ᵐ ∀ a, π' a
    where
  toEquiv := piCongrRight fun a => (e a).toEquiv
  measurable_to_fun :=
    measurable_pi_lambda _ fun i => (e i).measurable_to_fun.comp (measurable_pi_apply i)
  measurable_inv_fun :=
    measurable_pi_lambda _ fun i => (e i).measurable_inv_fun.comp (measurable_pi_apply i)
#align measurable_equiv.Pi_congr_right MeasurableEquiv.piCongrRight
-/

/- warning: measurable_equiv.pi_measurable_equiv_tprod -> MeasurableEquiv.piMeasurableEquivTProd is a dubious translation:
lean 3 declaration is
  forall {δ' : Type.{u_5}} {π : δ' -> Type.{u_7}} [_inst_5 : forall (x : δ'), MeasurableSpace.{u_7} (π x)] [_inst_7 : DecidableEq.{succ u_5} δ'] {l : List.{u_5} δ'}, (List.Nodup.{u_5} δ' l) -> (forall (i : δ'), Membership.Mem.{u_5, u_5} δ' (List.{u_5} δ') (List.hasMem.{u_5} δ') i l) -> (MeasurableEquiv.{max u_5 u_7, max u_7 u_1} (forall (i : δ'), π i) (List.TProd.{u_5, u_7, u_1} δ' π l) (MeasurableSpace.pi.{u_5, u_7} δ' (fun (i : δ') => π i) (fun (a : δ') => _inst_5 a)) (TProd.instMeasurableSpace.{u_5, u_7, u_1} δ' π (fun (a : δ') => _inst_5 a) l))
but is expected to have type
  forall {δ' : Type.{u_1}} {π : δ' -> Type.{u_2}} [_inst_5 : forall (x : δ'), MeasurableSpace.{u_2} (π x)] [_inst_7 : DecidableEq.{succ u_1} δ'] {l : List.{u_1} δ'}, (List.Nodup.{u_1} δ' l) -> (forall (i : δ'), Membership.mem.{u_1, u_1} δ' (List.{u_1} δ') (List.instMembershipList.{u_1} δ') i l) -> (MeasurableEquiv.{max u_1 u_2, u_2} (forall (i : δ'), π i) (List.TProd.{u_1, u_2} δ' π l) (MeasurableSpace.pi.{u_1, u_2} δ' (fun (i : δ') => π i) (fun (a : δ') => _inst_5 a)) (TProd.instMeasurableSpace.{u_1, u_2} δ' π (fun (a : δ') => _inst_5 a) l))
Case conversion may be inaccurate. Consider using '#align measurable_equiv.pi_measurable_equiv_tprod MeasurableEquiv.piMeasurableEquivTProdₓ'. -/
/-- Pi-types are measurably equivalent to iterated products. -/
@[simps (config := { fullyApplied := false })]
def piMeasurableEquivTProd [DecidableEq δ'] {l : List δ'} (hnd : l.Nodup) (h : ∀ i, i ∈ l) :
    (∀ i, π i) ≃ᵐ List.TProd π l
    where
  toEquiv := List.TProd.piEquivTProd hnd h
  measurable_to_fun := measurable_tProd_mk l
  measurable_inv_fun := measurable_tProd_elim' h
#align measurable_equiv.pi_measurable_equiv_tprod MeasurableEquiv.piMeasurableEquivTProd

#print MeasurableEquiv.funUnique /-
/-- If `α` has a unique term, then the type of function `α → β` is measurably equivalent to `β`. -/
@[simps (config := { fullyApplied := false })]
def funUnique (α β : Type _) [Unique α] [MeasurableSpace β] : (α → β) ≃ᵐ β
    where
  toEquiv := Equiv.funUnique α β
  measurable_to_fun := measurable_pi_apply _
  measurable_inv_fun := measurable_pi_iff.2 fun b => measurable_id
#align measurable_equiv.fun_unique MeasurableEquiv.funUnique
-/

/- warning: measurable_equiv.pi_fin_two -> MeasurableEquiv.piFinTwo is a dubious translation:
lean 3 declaration is
  forall (α : (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}) [_inst_7 : forall (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))), MeasurableSpace.{u1} (α i)], MeasurableEquiv.{u1, u1} (forall (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))), α i) (Prod.{u1, u1} (α (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) MeasurableEquiv.piFinTwo._proof_1))))) (α (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) MeasurableEquiv.piFinTwo._proof_2)))))) (MeasurableSpace.pi.{0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => α i) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => _inst_7 a)) (Prod.instMeasurableSpace.{u1, u1} (α (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) MeasurableEquiv.piFinTwo._proof_1))))) (α (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) MeasurableEquiv.piFinTwo._proof_2))))) (_inst_7 (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) MeasurableEquiv.piFinTwo._proof_1))))) (_inst_7 (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) MeasurableEquiv.piFinTwo._proof_2))))))
but is expected to have type
  forall (α : (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> Type.{u1}) [_inst_7 : forall (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))), MeasurableSpace.{u1} (α i)], MeasurableEquiv.{u1, u1} (forall (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))), α i) (Prod.{u1, u1} (α (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (α (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (MeasurableSpace.pi.{0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => α i) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => _inst_7 a)) (Prod.instMeasurableSpace.{u1, u1} (α (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (α (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (_inst_7 (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (_inst_7 (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align measurable_equiv.pi_fin_two MeasurableEquiv.piFinTwoₓ'. -/
/-- The space `Π i : fin 2, α i` is measurably equivalent to `α 0 × α 1`. -/
@[simps (config := { fullyApplied := false })]
def piFinTwo (α : Fin 2 → Type _) [∀ i, MeasurableSpace (α i)] : (∀ i, α i) ≃ᵐ α 0 × α 1
    where
  toEquiv := piFinTwoEquiv α
  measurable_to_fun := Measurable.prod (measurable_pi_apply _) (measurable_pi_apply _)
  measurable_inv_fun := measurable_pi_iff.2 <| Fin.forall_fin_two.2 ⟨measurable_fst, measurable_snd⟩
#align measurable_equiv.pi_fin_two MeasurableEquiv.piFinTwo

#print MeasurableEquiv.finTwoArrow /-
/-- The space `fin 2 → α` is measurably equivalent to `α × α`. -/
@[simps (config := { fullyApplied := false })]
def finTwoArrow : (Fin 2 → α) ≃ᵐ α × α :=
  piFinTwo fun _ => α
#align measurable_equiv.fin_two_arrow MeasurableEquiv.finTwoArrow
-/

/- warning: measurable_equiv.pi_fin_succ_above_equiv -> MeasurableEquiv.piFinSuccAboveEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measurable_equiv.pi_fin_succ_above_equiv MeasurableEquiv.piFinSuccAboveEquivₓ'. -/
/-- Measurable equivalence between `Π j : fin (n + 1), α j` and
`α i × Π j : fin n, α (fin.succ_above i j)`. -/
@[simps (config := { fullyApplied := false })]
def piFinSuccAboveEquiv {n : ℕ} (α : Fin (n + 1) → Type _) [∀ i, MeasurableSpace (α i)]
    (i : Fin (n + 1)) : (∀ j, α j) ≃ᵐ α i × ∀ j, α (i.succAbove j)
    where
  toEquiv := piFinSuccAboveEquiv α i
  measurable_to_fun :=
    (measurable_pi_apply i).prod_mk <| measurable_pi_iff.2 fun j => measurable_pi_apply _
  measurable_inv_fun := by
    simp [measurable_pi_iff, i.forall_iff_succ_above, measurable_fst,
      (measurable_pi_apply _).comp measurable_snd]
#align measurable_equiv.pi_fin_succ_above_equiv MeasurableEquiv.piFinSuccAboveEquiv

variable (π)

#print MeasurableEquiv.piEquivPiSubtypeProd /-
/-- Measurable equivalence between (dependent) functions on a type and pairs of functions on
`{i // p i}` and `{i // ¬p i}`. See also `equiv.pi_equiv_pi_subtype_prod`. -/
@[simps (config := { fullyApplied := false })]
def piEquivPiSubtypeProd (p : δ' → Prop) [DecidablePred p] :
    (∀ i, π i) ≃ᵐ (∀ i : Subtype p, π i) × ∀ i : { i // ¬p i }, π i
    where
  toEquiv := piEquivPiSubtypeProd p π
  measurable_to_fun := measurable_piEquivPiSubtypeProd π p
  measurable_inv_fun := measurable_piEquivPiSubtypeProd_symm π p
#align measurable_equiv.pi_equiv_pi_subtype_prod MeasurableEquiv.piEquivPiSubtypeProd
-/

/- warning: measurable_equiv.sum_compl -> MeasurableEquiv.sumCompl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {s : Set.{u1} α} [_inst_7 : DecidablePred.{succ u1} α s], (MeasurableSet.{u1} α _inst_1 s) -> (MeasurableEquiv.{u1, u1} (Sum.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) α (Sum.instMeasurableSpace.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) _inst_1)) _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {s : Set.{u1} α} [_inst_7 : DecidablePred.{succ u1} α (fun (x._@.Mathlib.MeasureTheory.MeasurableSpace._hyg.17408 : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x._@.Mathlib.MeasureTheory.MeasurableSpace._hyg.17408 s)], (MeasurableSet.{u1} α _inst_1 s) -> (MeasurableEquiv.{u1, u1} (Sum.{u1, u1} (Set.Elem.{u1} α s) (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))) α (Sum.instMeasurableSpace.{u1, u1} (Set.Elem.{u1} α s) (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) _inst_1) (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) _inst_1)) _inst_1)
Case conversion may be inaccurate. Consider using '#align measurable_equiv.sum_compl MeasurableEquiv.sumComplₓ'. -/
/-- If `s` is a measurable set in a measurable space, that space is equivalent
to the sum of `s` and `sᶜ`.-/
def sumCompl {s : Set α} [DecidablePred s] (hs : MeasurableSet s) : Sum s (sᶜ : Set α) ≃ᵐ α
    where
  toEquiv := sumCompl s
  measurable_to_fun := by apply Measurable.sumElim <;> exact measurable_subtype_coe
  measurable_inv_fun := Measurable.dite measurable_inl measurable_inr hs
#align measurable_equiv.sum_compl MeasurableEquiv.sumCompl

end MeasurableEquiv

namespace MeasurableEmbedding

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {g : β → α}

#print MeasurableEmbedding.equivImage /-
/-- A set is equivalent to its image under a function `f` as measurable spaces,
  if `f` is a measurable embedding -/
noncomputable def equivImage (s : Set α) (hf : MeasurableEmbedding f) : s ≃ᵐ f '' s
    where
  toEquiv := Equiv.Set.image f s hf.Injective
  measurable_to_fun := (hf.Measurable.comp measurable_id.subtype_val).subtype_mk
  measurable_inv_fun := by
    rintro t ⟨u, hu, rfl⟩; simp [preimage_preimage, set.image_symm_preimage hf.injective]
    exact measurable_subtype_coe (hf.measurable_set_image' hu)
#align measurable_embedding.equiv_image MeasurableEmbedding.equivImage
-/

#print MeasurableEmbedding.equivRange /-
/-- The domain of `f` is equivalent to its range as measurable spaces,
  if `f` is a measurable embedding -/
noncomputable def equivRange (hf : MeasurableEmbedding f) : α ≃ᵐ range f :=
  (MeasurableEquiv.Set.univ _).symm.trans <|
    (hf.equivImage univ).trans <| MeasurableEquiv.cast (by rw [image_univ]) (by rw [image_univ])
#align measurable_embedding.equiv_range MeasurableEmbedding.equivRange
-/

#print MeasurableEmbedding.of_measurable_inverse_on_range /-
theorem of_measurable_inverse_on_range {g : range f → α} (hf₁ : Measurable f)
    (hf₂ : MeasurableSet (range f)) (hg : Measurable g) (H : LeftInverse g (rangeFactorization f)) :
    MeasurableEmbedding f :=
  by
  set e : α ≃ᵐ range f :=
    ⟨⟨range_factorization f, g, H, H.right_inverse_of_surjective surjective_onto_range⟩,
      hf₁.subtype_mk, hg⟩
  exact (MeasurableEmbedding.subtype_coe hf₂).comp e.measurable_embedding
#align measurable_embedding.of_measurable_inverse_on_range MeasurableEmbedding.of_measurable_inverse_on_range
-/

/- warning: measurable_embedding.of_measurable_inverse -> MeasurableEmbedding.of_measurable_inverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {f : α -> β} {g : β -> α}, (Measurable.{u1, u2} α β _inst_1 _inst_2 f) -> (MeasurableSet.{u2} β _inst_2 (Set.range.{u2, succ u1} β α f)) -> (Measurable.{u2, u1} β α _inst_2 _inst_1 g) -> (Function.LeftInverse.{succ u1, succ u2} α β g f) -> (MeasurableEmbedding.{u1, u2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {f : α -> β} {g : β -> α}, (Measurable.{u2, u1} α β _inst_1 _inst_2 f) -> (MeasurableSet.{u1} β _inst_2 (Set.range.{u1, succ u2} β α f)) -> (Measurable.{u1, u2} β α _inst_2 _inst_1 g) -> (Function.LeftInverse.{succ u2, succ u1} α β g f) -> (MeasurableEmbedding.{u2, u1} α β _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align measurable_embedding.of_measurable_inverse MeasurableEmbedding.of_measurable_inverseₓ'. -/
theorem of_measurable_inverse (hf₁ : Measurable f) (hf₂ : MeasurableSet (range f))
    (hg : Measurable g) (H : LeftInverse g f) : MeasurableEmbedding f :=
  of_measurable_inverse_on_range hf₁ hf₂ (hg.comp measurable_subtype_coe) H
#align measurable_embedding.of_measurable_inverse MeasurableEmbedding.of_measurable_inverse

open Classical

#print MeasurableEmbedding.schroederBernstein /-
/-- The **`measurable Schröder-Bernstein Theorem**: Given measurable embeddings
`α → β` and `β → α`, we can find a measurable equivalence `α ≃ᵐ β`.-/
noncomputable def schroederBernstein {f : α → β} {g : β → α} (hf : MeasurableEmbedding f)
    (hg : MeasurableEmbedding g) : α ≃ᵐ β :=
  by
  let F : Set α → Set α := fun A => (g '' (f '' A)ᶜ)ᶜ
  -- We follow the proof of the usual SB theorem in mathlib,
  -- the crux of which is finding a fixed point of this F.
  -- However, we must find this fixed point manually instead of invoking Knaster-Tarski
  -- in order to make sure it is measurable.
  suffices Σ'A : Set α, MeasurableSet A ∧ F A = A
    by
    rcases this with ⟨A, Ameas, Afp⟩
    let B := f '' A
    have Bmeas : MeasurableSet B := hf.measurable_set_image' Ameas
    refine'
      (MeasurableEquiv.sumCompl Ameas).symm.trans
        (MeasurableEquiv.trans _ (MeasurableEquiv.sumCompl Bmeas))
    apply MeasurableEquiv.sumCongr (hf.equiv_image _)
    have : Aᶜ = g '' Bᶜ := by
      apply compl_injective
      rw [← Afp]
      simp
    rw [this]
    exact (hg.equiv_image _).symm
  have Fmono : ∀ {A B}, A ⊆ B → F A ⊆ F B := fun A B hAB =>
    compl_subset_compl.mpr <| Set.image_subset _ <| compl_subset_compl.mpr <| Set.image_subset _ hAB
  let X : ℕ → Set α := fun n => (F^[n]) univ
  refine' ⟨Inter X, _, _⟩
  · apply MeasurableSet.iInter
    intro n
    induction' n with n ih
    · exact MeasurableSet.univ
    rw [Function.iterate_succ', Function.comp_apply]
    exact (hg.measurable_set_image' (hf.measurable_set_image' ih).compl).compl
  apply subset_antisymm
  · apply subset_Inter
    intro n
    cases n
    · exact subset_univ _
    rw [Function.iterate_succ', Function.comp_apply]
    exact Fmono (Inter_subset _ _)
  rintro x hx ⟨y, hy, rfl⟩
  rw [mem_Inter] at hx
  apply hy
  rw [(inj_on_of_injective hf.injective _).image_iInter_eq]
  swap
  · infer_instance
  rw [mem_Inter]
  intro n
  specialize hx n.succ
  rw [Function.iterate_succ', Function.comp_apply] at hx
  by_contra h
  apply hx
  exact ⟨y, h, rfl⟩
#align measurable_embedding.schroeder_bernstein MeasurableEmbedding.schroederBernstein
-/

end MeasurableEmbedding

section CountablyGenerated

namespace MeasurableSpace

variable (α)

#print MeasurableSpace.CountablyGenerated /-
/-- We say a measurable space is countably generated
if can be generated by a countable set of sets.-/
class CountablyGenerated [m : MeasurableSpace α] : Prop where
  IsCountablyGenerated : ∃ b : Set (Set α), b.Countable ∧ m = generateFrom b
#align measurable_space.countably_generated MeasurableSpace.CountablyGenerated
-/

open Classical

#print MeasurableSpace.measurable_injection_nat_bool_of_countablyGenerated /-
/-- If a measurable space is countably generated, it admits a measurable injection
into the Cantor space `ℕ → bool` (equipped with the product sigma algebra). -/
theorem measurable_injection_nat_bool_of_countablyGenerated [MeasurableSpace α]
    [h : CountablyGenerated α] [MeasurableSingletonClass α] :
    ∃ f : α → ℕ → Bool, Measurable f ∧ Function.Injective f :=
  by
  obtain ⟨b, bct, hb⟩ := h.is_countably_generated
  obtain ⟨e, he⟩ := Set.Countable.exists_eq_range (bct.insert ∅) (insert_nonempty _ _)
  rw [← generate_from_insert_empty, he] at hb
  refine' ⟨fun x n => to_bool (x ∈ e n), _, _⟩
  · rw [measurable_pi_iff]
    intro n
    apply measurable_to_bool
    simp only [preimage, mem_singleton_iff, Bool.decide_iff, set_of_mem_eq]
    rw [hb]
    apply measurable_set_generate_from
    use n
  intro x y hxy
  have : ∀ s : Set α, MeasurableSet s → (x ∈ s ↔ y ∈ s) := fun s =>
    by
    rw [hb]
    apply generate_from_induction
    · rintro - ⟨n, rfl⟩
      rw [← decide_eq_decide]
      rw [funext_iff] at hxy
      exact hxy n
    · tauto
    · intro t
      tauto
    intro t ht
    simp_rw [mem_Union, ht]
  specialize this {y} measurableSet_eq
  simpa only [mem_singleton, iff_true_iff]
#align measurable_space.measurable_injection_nat_bool_of_countably_generated MeasurableSpace.measurable_injection_nat_bool_of_countablyGenerated
-/

end MeasurableSpace

end CountablyGenerated

namespace Filter

variable [MeasurableSpace α]

#print Filter.IsMeasurablyGenerated /-
/-- A filter `f` is measurably generates if each `s ∈ f` includes a measurable `t ∈ f`. -/
class IsMeasurablyGenerated (f : Filter α) : Prop where
  exists_measurable_subset : ∀ ⦃s⦄, s ∈ f → ∃ t ∈ f, MeasurableSet t ∧ t ⊆ s
#align filter.is_measurably_generated Filter.IsMeasurablyGenerated
-/

/- warning: filter.is_measurably_generated_bot -> Filter.isMeasurablyGenerated_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α], Filter.IsMeasurablyGenerated.{u1} α _inst_1 (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α], Filter.IsMeasurablyGenerated.{u1} α _inst_1 (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))
Case conversion may be inaccurate. Consider using '#align filter.is_measurably_generated_bot Filter.isMeasurablyGenerated_botₓ'. -/
instance isMeasurablyGenerated_bot : IsMeasurablyGenerated (⊥ : Filter α) :=
  ⟨fun _ _ => ⟨∅, mem_bot, MeasurableSet.empty, empty_subset _⟩⟩
#align filter.is_measurably_generated_bot Filter.isMeasurablyGenerated_bot

/- warning: filter.is_measurably_generated_top -> Filter.isMeasurablyGenerated_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α], Filter.IsMeasurablyGenerated.{u1} α _inst_1 (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α], Filter.IsMeasurablyGenerated.{u1} α _inst_1 (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))
Case conversion may be inaccurate. Consider using '#align filter.is_measurably_generated_top Filter.isMeasurablyGenerated_topₓ'. -/
instance isMeasurablyGenerated_top : IsMeasurablyGenerated (⊤ : Filter α) :=
  ⟨fun s hs => ⟨univ, univ_mem, MeasurableSet.univ, fun x _ => hs x⟩⟩
#align filter.is_measurably_generated_top Filter.isMeasurablyGenerated_top

/- warning: filter.eventually.exists_measurable_mem -> Filter.Eventually.exists_measurable_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {f : Filter.{u1} α} [_inst_2 : Filter.IsMeasurablyGenerated.{u1} α _inst_1 f] {p : α -> Prop}, (Filter.Eventually.{u1} α (fun (x : α) => p x) f) -> (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) => And (MeasurableSet.{u1} α _inst_1 s) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (p x)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {f : Filter.{u1} α} [_inst_2 : Filter.IsMeasurablyGenerated.{u1} α _inst_1 f] {p : α -> Prop}, (Filter.Eventually.{u1} α (fun (x : α) => p x) f) -> (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) (And (MeasurableSet.{u1} α _inst_1 s) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (p x)))))
Case conversion may be inaccurate. Consider using '#align filter.eventually.exists_measurable_mem Filter.Eventually.exists_measurable_memₓ'. -/
theorem Eventually.exists_measurable_mem {f : Filter α} [IsMeasurablyGenerated f] {p : α → Prop}
    (h : ∀ᶠ x in f, p x) : ∃ s ∈ f, MeasurableSet s ∧ ∀ x ∈ s, p x :=
  IsMeasurablyGenerated.exists_measurable_subset h
#align filter.eventually.exists_measurable_mem Filter.Eventually.exists_measurable_mem

/- warning: filter.eventually.exists_measurable_mem_of_small_sets -> Filter.Eventually.exists_measurable_mem_of_smallSets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {f : Filter.{u1} α} [_inst_2 : Filter.IsMeasurablyGenerated.{u1} α _inst_1 f] {p : (Set.{u1} α) -> Prop}, (Filter.Eventually.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => p s) (Filter.smallSets.{u1} α f)) -> (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) => And (MeasurableSet.{u1} α _inst_1 s) (p s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {f : Filter.{u1} α} [_inst_2 : Filter.IsMeasurablyGenerated.{u1} α _inst_1 f] {p : (Set.{u1} α) -> Prop}, (Filter.Eventually.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => p s) (Filter.smallSets.{u1} α f)) -> (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) (And (MeasurableSet.{u1} α _inst_1 s) (p s))))
Case conversion may be inaccurate. Consider using '#align filter.eventually.exists_measurable_mem_of_small_sets Filter.Eventually.exists_measurable_mem_of_smallSetsₓ'. -/
theorem Eventually.exists_measurable_mem_of_smallSets {f : Filter α} [IsMeasurablyGenerated f]
    {p : Set α → Prop} (h : ∀ᶠ s in f.smallSets, p s) : ∃ s ∈ f, MeasurableSet s ∧ p s :=
  let ⟨s, hsf, hs⟩ := eventually_smallSets.1 h
  let ⟨t, htf, htm, hts⟩ := IsMeasurablyGenerated.exists_measurable_subset hsf
  ⟨t, htf, htm, hs t hts⟩
#align filter.eventually.exists_measurable_mem_of_small_sets Filter.Eventually.exists_measurable_mem_of_smallSets

/- warning: filter.inf_is_measurably_generated -> Filter.inf_isMeasurablyGenerated is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : Filter.{u1} α) (g : Filter.{u1} α) [_inst_2 : Filter.IsMeasurablyGenerated.{u1} α _inst_1 f] [_inst_3 : Filter.IsMeasurablyGenerated.{u1} α _inst_1 g], Filter.IsMeasurablyGenerated.{u1} α _inst_1 (Inf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f g)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : Filter.{u1} α) (g : Filter.{u1} α) [_inst_2 : Filter.IsMeasurablyGenerated.{u1} α _inst_1 f] [_inst_3 : Filter.IsMeasurablyGenerated.{u1} α _inst_1 g], Filter.IsMeasurablyGenerated.{u1} α _inst_1 (Inf.inf.{u1} (Filter.{u1} α) (Filter.instInfFilter.{u1} α) f g)
Case conversion may be inaccurate. Consider using '#align filter.inf_is_measurably_generated Filter.inf_isMeasurablyGeneratedₓ'. -/
instance inf_isMeasurablyGenerated (f g : Filter α) [IsMeasurablyGenerated f]
    [IsMeasurablyGenerated g] : IsMeasurablyGenerated (f ⊓ g) :=
  by
  refine' ⟨_⟩
  rintro t ⟨sf, hsf, sg, hsg, rfl⟩
  rcases is_measurably_generated.exists_measurable_subset hsf with ⟨s'f, hs'f, hmf, hs'sf⟩
  rcases is_measurably_generated.exists_measurable_subset hsg with ⟨s'g, hs'g, hmg, hs'sg⟩
  refine' ⟨s'f ∩ s'g, inter_mem_inf hs'f hs'g, hmf.inter hmg, _⟩
  exact inter_subset_inter hs'sf hs'sg
#align filter.inf_is_measurably_generated Filter.inf_isMeasurablyGenerated

#print Filter.principal_isMeasurablyGenerated_iff /-
theorem principal_isMeasurablyGenerated_iff {s : Set α} :
    IsMeasurablyGenerated (𝓟 s) ↔ MeasurableSet s :=
  by
  refine' ⟨_, fun hs => ⟨fun t ht => ⟨s, mem_principal_self s, hs, ht⟩⟩⟩
  rintro ⟨hs⟩
  rcases hs (mem_principal_self s) with ⟨t, ht, htm, hts⟩
  have : t = s := subset.antisymm hts ht
  rwa [← this]
#align filter.principal_is_measurably_generated_iff Filter.principal_isMeasurablyGenerated_iff
-/

alias principal_is_measurably_generated_iff ↔
  _ _root_.measurable_set.principal_is_measurably_generated
#align measurable_set.principal_is_measurably_generated MeasurableSet.principal_isMeasurablyGenerated

/- warning: filter.infi_is_measurably_generated -> Filter.iInf_isMeasurablyGenerated is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {f : ι -> (Filter.{u1} α)} [_inst_2 : forall (i : ι), Filter.IsMeasurablyGenerated.{u1} α _inst_1 (f i)], Filter.IsMeasurablyGenerated.{u1} α _inst_1 (iInf.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {f : ι -> (Filter.{u2} α)} [_inst_2 : forall (i : ι), Filter.IsMeasurablyGenerated.{u2} α _inst_1 (f i)], Filter.IsMeasurablyGenerated.{u2} α _inst_1 (iInf.{u2, u1} (Filter.{u2} α) (ConditionallyCompleteLattice.toInfSet.{u2} (Filter.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α))) ι (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align filter.infi_is_measurably_generated Filter.iInf_isMeasurablyGeneratedₓ'. -/
instance iInf_isMeasurablyGenerated {f : ι → Filter α} [∀ i, IsMeasurablyGenerated (f i)] :
    IsMeasurablyGenerated (⨅ i, f i) :=
  by
  refine' ⟨fun s hs => _⟩
  rw [← equiv.plift.surjective.infi_comp, mem_infi] at hs
  rcases hs with ⟨t, ht, ⟨V, hVf, rfl⟩⟩
  choose U hUf hU using fun i => is_measurably_generated.exists_measurable_subset (hVf i)
  refine' ⟨⋂ i : t, U i, _, _, _⟩
  · rw [← equiv.plift.surjective.infi_comp, mem_infi]
    refine' ⟨t, ht, U, hUf, rfl⟩
  · haveI := ht.countable.to_encodable
    exact MeasurableSet.iInter fun i => (hU i).1
  · exact Inter_mono fun i => (hU i).2
#align filter.infi_is_measurably_generated Filter.iInf_isMeasurablyGenerated

end Filter

#print IsCountablySpanning /-
/-- We say that a collection of sets is countably spanning if a countable subset spans the
  whole type. This is a useful condition in various parts of measure theory. For example, it is
  a needed condition to show that the product of two collections generate the product sigma algebra,
  see `generate_from_prod_eq`. -/
def IsCountablySpanning (C : Set (Set α)) : Prop :=
  ∃ s : ℕ → Set α, (∀ n, s n ∈ C) ∧ (⋃ n, s n) = univ
#align is_countably_spanning IsCountablySpanning
-/

#print isCountablySpanning_measurableSet /-
theorem isCountablySpanning_measurableSet [MeasurableSpace α] :
    IsCountablySpanning { s : Set α | MeasurableSet s } :=
  ⟨fun _ => univ, fun _ => MeasurableSet.univ, iUnion_const _⟩
#align is_countably_spanning_measurable_set isCountablySpanning_measurableSet
-/

namespace MeasurableSet

/-!
### Typeclasses on `subtype measurable_set`
-/


variable [MeasurableSpace α]

instance : Membership α (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun a s => a ∈ (s : Set α)⟩

#print MeasurableSet.mem_coe /-
@[simp]
theorem mem_coe (a : α) (s : Subtype (MeasurableSet : Set α → Prop)) : a ∈ (s : Set α) ↔ a ∈ s :=
  Iff.rfl
#align measurable_set.mem_coe MeasurableSet.mem_coe
-/

instance : EmptyCollection (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨⟨∅, MeasurableSet.empty⟩⟩

#print MeasurableSet.coe_empty /-
@[simp]
theorem coe_empty : ↑(∅ : Subtype (MeasurableSet : Set α → Prop)) = (∅ : Set α) :=
  rfl
#align measurable_set.coe_empty MeasurableSet.coe_empty
-/

instance [MeasurableSingletonClass α] : Insert α (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun a s => ⟨Insert.insert a s, s.Prop.insert a⟩⟩

#print MeasurableSet.coe_insert /-
@[simp]
theorem coe_insert [MeasurableSingletonClass α] (a : α)
    (s : Subtype (MeasurableSet : Set α → Prop)) :
    ↑(Insert.insert a s) = (Insert.insert a s : Set α) :=
  rfl
#align measurable_set.coe_insert MeasurableSet.coe_insert
-/

instance : HasCompl (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x => ⟨xᶜ, x.Prop.compl⟩⟩

/- warning: measurable_set.coe_compl -> MeasurableSet.coe_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (s : Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeBase.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 x))))) (HasCompl.compl.{u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (MeasurableSet.Subtype.instHasCompl.{u1} α _inst_1) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeBase.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 x))))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (s : Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)), Eq.{succ u1} (Set.{u1} α) (Subtype.val.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1) (HasCompl.compl.{u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (MeasurableSet.Subtype.instHasCompl.{u1} α _inst_1) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Subtype.val.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align measurable_set.coe_compl MeasurableSet.coe_complₓ'. -/
@[simp]
theorem coe_compl (s : Subtype (MeasurableSet : Set α → Prop)) : ↑(sᶜ) = (sᶜ : Set α) :=
  rfl
#align measurable_set.coe_compl MeasurableSet.coe_compl

instance : Union (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => ⟨x ∪ y, x.Prop.union y.Prop⟩⟩

/- warning: measurable_set.coe_union -> MeasurableSet.coe_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (s : Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (t : Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeBase.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 x))))) (Union.union.{u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (MeasurableSet.Subtype.instUnion.{u1} α _inst_1) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeBase.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 x))))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeBase.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 x))))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (s : Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (t : Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)), Eq.{succ u1} (Set.{u1} α) (Subtype.val.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1) (Union.union.{u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (MeasurableSet.Subtype.instUnion.{u1} α _inst_1) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Subtype.val.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1) s) (Subtype.val.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align measurable_set.coe_union MeasurableSet.coe_unionₓ'. -/
@[simp]
theorem coe_union (s t : Subtype (MeasurableSet : Set α → Prop)) : ↑(s ∪ t) = (s ∪ t : Set α) :=
  rfl
#align measurable_set.coe_union MeasurableSet.coe_union

instance : Inter (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => ⟨x ∩ y, x.Prop.inter y.Prop⟩⟩

/- warning: measurable_set.coe_inter -> MeasurableSet.coe_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (s : Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (t : Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeBase.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 x))))) (Inter.inter.{u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (MeasurableSet.Subtype.instInter.{u1} α _inst_1) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeBase.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 x))))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeBase.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 x))))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (s : Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (t : Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)), Eq.{succ u1} (Set.{u1} α) (Subtype.val.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1) (Inter.inter.{u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (MeasurableSet.Subtype.instInter.{u1} α _inst_1) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Subtype.val.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1) s) (Subtype.val.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align measurable_set.coe_inter MeasurableSet.coe_interₓ'. -/
@[simp]
theorem coe_inter (s t : Subtype (MeasurableSet : Set α → Prop)) : ↑(s ∩ t) = (s ∩ t : Set α) :=
  rfl
#align measurable_set.coe_inter MeasurableSet.coe_inter

instance : SDiff (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨fun x y => ⟨x \ y, x.Prop.diffₓ y.Prop⟩⟩

/- warning: measurable_set.coe_sdiff -> MeasurableSet.coe_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (s : Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (t : Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeBase.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 x))))) (SDiff.sdiff.{u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (MeasurableSet.Subtype.instSDiff.{u1} α _inst_1) s t)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeBase.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 x))))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeBase.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 x))))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (s : Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (t : Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)), Eq.{succ u1} (Set.{u1} α) (Subtype.val.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1) (SDiff.sdiff.{u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (MeasurableSet.Subtype.instSDiff.{u1} α _inst_1) s t)) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Subtype.val.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1) s) (Subtype.val.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align measurable_set.coe_sdiff MeasurableSet.coe_sdiffₓ'. -/
@[simp]
theorem coe_sdiff (s t : Subtype (MeasurableSet : Set α → Prop)) : ↑(s \ t) = (s \ t : Set α) :=
  rfl
#align measurable_set.coe_sdiff MeasurableSet.coe_sdiff

instance : Bot (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨⟨⊥, MeasurableSet.empty⟩⟩

/- warning: measurable_set.coe_bot -> MeasurableSet.coe_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeBase.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 x))))) (Bot.bot.{u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (MeasurableSet.Subtype.instBot.{u1} α _inst_1))) (Bot.bot.{u1} (Set.{u1} α) (CompleteLattice.toHasBot.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) (Subtype.val.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1) (Bot.bot.{u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (MeasurableSet.Subtype.instBot.{u1} α _inst_1))) (Bot.bot.{u1} (Set.{u1} α) (CompleteLattice.toBot.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))
Case conversion may be inaccurate. Consider using '#align measurable_set.coe_bot MeasurableSet.coe_botₓ'. -/
@[simp]
theorem coe_bot : ↑(⊥ : Subtype (MeasurableSet : Set α → Prop)) = (⊥ : Set α) :=
  rfl
#align measurable_set.coe_bot MeasurableSet.coe_bot

instance : Top (Subtype (MeasurableSet : Set α → Prop)) :=
  ⟨⟨⊤, MeasurableSet.univ⟩⟩

/- warning: measurable_set.coe_top -> MeasurableSet.coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeBase.{succ u1, succ u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (Set.{u1} α) (coeSubtype.{succ u1} (Set.{u1} α) (fun (x : Set.{u1} α) => MeasurableSet.{u1} α _inst_1 x))))) (Top.top.{u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (MeasurableSet.Subtype.instTop.{u1} α _inst_1))) (Top.top.{u1} (Set.{u1} α) (CompleteLattice.toHasTop.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) (Subtype.val.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1) (Top.top.{u1} (Subtype.{succ u1} (Set.{u1} α) (MeasurableSet.{u1} α _inst_1)) (MeasurableSet.Subtype.instTop.{u1} α _inst_1))) (Top.top.{u1} (Set.{u1} α) (CompleteLattice.toTop.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))
Case conversion may be inaccurate. Consider using '#align measurable_set.coe_top MeasurableSet.coe_topₓ'. -/
@[simp]
theorem coe_top : ↑(⊤ : Subtype (MeasurableSet : Set α → Prop)) = (⊤ : Set α) :=
  rfl
#align measurable_set.coe_top MeasurableSet.coe_top

instance : PartialOrder (Subtype (MeasurableSet : Set α → Prop)) :=
  PartialOrder.lift _ Subtype.coe_injective

instance : DistribLattice (Subtype (MeasurableSet : Set α → Prop)) :=
  { MeasurableSet.Subtype.partialOrder with
    sup := (· ∪ ·)
    le_sup_left := fun a b => show (a : Set α) ≤ a ⊔ b from le_sup_left
    le_sup_right := fun a b => show (b : Set α) ≤ a ⊔ b from le_sup_right
    sup_le := fun a b c ha hb => show (a ⊔ b : Set α) ≤ c from sup_le ha hb
    inf := (· ∩ ·)
    inf_le_left := fun a b => show (a ⊓ b : Set α) ≤ a from inf_le_left
    inf_le_right := fun a b => show (a ⊓ b : Set α) ≤ b from inf_le_right
    le_inf := fun a b c ha hb => show (a : Set α) ≤ b ⊓ c from le_inf ha hb
    le_sup_inf := fun x y z => show ((x ⊔ y) ⊓ (x ⊔ z) : Set α) ≤ x ⊔ y ⊓ z from le_sup_inf }

instance : BoundedOrder (Subtype (MeasurableSet : Set α → Prop))
    where
  top := ⊤
  le_top a := show (a : Set α) ≤ ⊤ from le_top
  bot := ⊥
  bot_le a := show (⊥ : Set α) ≤ a from bot_le

instance : BooleanAlgebra (Subtype (MeasurableSet : Set α → Prop)) :=
  { MeasurableSet.Subtype.boundedOrder,
    MeasurableSet.Subtype.distribLattice with
    sdiff := (· \ ·)
    compl := HasCompl.compl
    inf_compl_le_bot := fun a => BooleanAlgebra.inf_compl_le_bot (a : Set α)
    top_le_sup_compl := fun a => BooleanAlgebra.top_le_sup_compl (a : Set α)
    sdiff_eq := fun a b => Subtype.eq <| sdiff_eq }

/- warning: measurable_set.measurable_set_blimsup -> MeasurableSet.measurableSet_blimsup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {s : Nat -> (Set.{u1} α)} {p : Nat -> Prop}, (forall (n : Nat), (p n) -> (MeasurableSet.{u1} α _inst_1 (s n))) -> (MeasurableSet.{u1} α _inst_1 (Filter.blimsup.{u1, 0} (Set.{u1} α) Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) s (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {s : Nat -> (Set.{u1} α)} {p : Nat -> Prop}, (forall (n : Nat), (p n) -> (MeasurableSet.{u1} α _inst_1 (s n))) -> (MeasurableSet.{u1} α _inst_1 (Filter.blimsup.{u1, 0} (Set.{u1} α) Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) s (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) p))
Case conversion may be inaccurate. Consider using '#align measurable_set.measurable_set_blimsup MeasurableSet.measurableSet_blimsupₓ'. -/
@[measurability]
theorem measurableSet_blimsup {s : ℕ → Set α} {p : ℕ → Prop} (h : ∀ n, p n → MeasurableSet (s n)) :
    MeasurableSet <| Filter.blimsup s Filter.atTop p :=
  by
  simp only [Filter.blimsup_eq_iInf_biSup_of_nat, supr_eq_Union, infi_eq_Inter]
  exact
    MeasurableSet.iInter fun n =>
      MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun hm => h m hm.1
#align measurable_set.measurable_set_blimsup MeasurableSet.measurableSet_blimsup

/- warning: measurable_set.measurable_set_bliminf -> MeasurableSet.measurableSet_bliminf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {s : Nat -> (Set.{u1} α)} {p : Nat -> Prop}, (forall (n : Nat), (p n) -> (MeasurableSet.{u1} α _inst_1 (s n))) -> (MeasurableSet.{u1} α _inst_1 (Filter.bliminf.{u1, 0} (Set.{u1} α) Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) s (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {s : Nat -> (Set.{u1} α)} {p : Nat -> Prop}, (forall (n : Nat), (p n) -> (MeasurableSet.{u1} α _inst_1 (s n))) -> (MeasurableSet.{u1} α _inst_1 (Filter.bliminf.{u1, 0} (Set.{u1} α) Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) s (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) p))
Case conversion may be inaccurate. Consider using '#align measurable_set.measurable_set_bliminf MeasurableSet.measurableSet_bliminfₓ'. -/
@[measurability]
theorem measurableSet_bliminf {s : ℕ → Set α} {p : ℕ → Prop} (h : ∀ n, p n → MeasurableSet (s n)) :
    MeasurableSet <| Filter.bliminf s Filter.atTop p :=
  by
  simp only [Filter.bliminf_eq_iSup_biInf_of_nat, infi_eq_Inter, supr_eq_Union]
  exact
    MeasurableSet.iUnion fun n =>
      MeasurableSet.iInter fun m => MeasurableSet.iInter fun hm => h m hm.1
#align measurable_set.measurable_set_bliminf MeasurableSet.measurableSet_bliminf

/- warning: measurable_set.measurable_set_limsup -> MeasurableSet.measurableSet_limsup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {s : Nat -> (Set.{u1} α)}, (forall (n : Nat), MeasurableSet.{u1} α _inst_1 (s n)) -> (MeasurableSet.{u1} α _inst_1 (Filter.limsup.{u1, 0} (Set.{u1} α) Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) s (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {s : Nat -> (Set.{u1} α)}, (forall (n : Nat), MeasurableSet.{u1} α _inst_1 (s n)) -> (MeasurableSet.{u1} α _inst_1 (Filter.limsup.{u1, 0} (Set.{u1} α) Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) s (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))))
Case conversion may be inaccurate. Consider using '#align measurable_set.measurable_set_limsup MeasurableSet.measurableSet_limsupₓ'. -/
@[measurability]
theorem measurableSet_limsup {s : ℕ → Set α} (hs : ∀ n, MeasurableSet <| s n) :
    MeasurableSet <| Filter.limsup s Filter.atTop :=
  by
  convert measurable_set_blimsup (fun n h => hs n : ∀ n, True → MeasurableSet (s n))
  simp
#align measurable_set.measurable_set_limsup MeasurableSet.measurableSet_limsup

/- warning: measurable_set.measurable_set_liminf -> MeasurableSet.measurableSet_liminf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {s : Nat -> (Set.{u1} α)}, (forall (n : Nat), MeasurableSet.{u1} α _inst_1 (s n)) -> (MeasurableSet.{u1} α _inst_1 (Filter.liminf.{u1, 0} (Set.{u1} α) Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) s (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {s : Nat -> (Set.{u1} α)}, (forall (n : Nat), MeasurableSet.{u1} α _inst_1 (s n)) -> (MeasurableSet.{u1} α _inst_1 (Filter.liminf.{u1, 0} (Set.{u1} α) Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) s (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))))
Case conversion may be inaccurate. Consider using '#align measurable_set.measurable_set_liminf MeasurableSet.measurableSet_liminfₓ'. -/
@[measurability]
theorem measurableSet_liminf {s : ℕ → Set α} (hs : ∀ n, MeasurableSet <| s n) :
    MeasurableSet <| Filter.liminf s Filter.atTop :=
  by
  convert measurable_set_bliminf (fun n h => hs n : ∀ n, True → MeasurableSet (s n))
  simp
#align measurable_set.measurable_set_liminf MeasurableSet.measurableSet_liminf

end MeasurableSet

