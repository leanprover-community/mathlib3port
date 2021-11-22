import Mathbin.Data.Finset.Lattice 
import Mathbin.Data.Set.Pairwise

/-!
# Finite supremum independence

In this file, we define supremum independence of indexed sets. An indexed family `f : ι → α` is
sup-independent if, for all `a`, `f a` and the supremum of the rest are disjoint.

In distributive lattices, this is equivalent to being pairwise disjoint.

## TODO

As we don't have `lattice_bot`, we're forced to pick between `bounded_lattice` (which assumes `top`
unnecessarily) and `distrib_lattice_bot` (which assumes distributivity unnecessarily). For now we
pick `distrib_lattice_bot` for it to apply to `finset α`, although this use is redundant with
`set.pairwise_disjoint`.

`complete_lattice.independent` and `complete_lattice.set_independent` should live in this file.
-/


variable{α β ι ι' : Type _}

namespace Finset

variable[DistribLatticeBot α][DecidableEq ι][DecidableEq ι']

/-- Supremum independence of finite sets. -/
def sup_indep (s : Finset ι) (f : ι → α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → Disjoint (f a) ((s.erase a).sup f)

variable{s t : Finset ι}{f : ι → α}

theorem sup_indep.subset (ht : t.sup_indep f) (h : s ⊆ t) : s.sup_indep f :=
  fun a ha => (ht$ h ha).mono_right$ sup_mono$ erase_subset_erase _ h

theorem sup_indep_empty (f : ι → α) : (∅ : Finset ι).SupIndep f :=
  fun a ha => ha.elim

theorem sup_indep_singleton (i : ι) (f : ι → α) : ({i} : Finset ι).SupIndep f :=
  fun j hj =>
    by 
      rw [mem_singleton.1 hj, erase_singleton, sup_empty]
      exact disjoint_bot_right

theorem sup_indep.attach (hs : s.sup_indep f) : s.attach.sup_indep (f ∘ Subtype.val) :=
  fun i _ =>
    by 
      rw [←Finset.sup_image, image_erase Subtype.val_injective, attach_image_val]
      exact hs i.2

/-- Bind operation for `sup_indep`. -/
theorem sup_indep.sup {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α} (hs : s.sup_indep fun i => (g i).sup f)
  (hg : ∀ i' _ : i' ∈ s, (g i').SupIndep f) : (s.sup g).SupIndep f :=
  by 
    rintro i hi 
    rw [disjoint_sup_right]
    refine' fun j hj => _ 
    rw [mem_sup] at hi 
    obtain ⟨i', hi', hi⟩ := hi 
    rw [mem_erase, mem_sup] at hj 
    obtain ⟨hij, j', hj', hj⟩ := hj 
    obtain hij' | hij' := eq_or_ne j' i'
    ·
      exact disjoint_sup_right.1 (hg i' hi' hi) _ (mem_erase.2 ⟨hij, hij'.subst hj⟩)
    ·
      exact (hs hi').mono (le_sup hi) ((le_sup hj).trans$ le_sup$ mem_erase.2 ⟨hij', hj'⟩)

/-- Bind operation for `sup_indep`. -/
theorem sup_indep.bUnion {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α} (hs : s.sup_indep fun i => (g i).sup f)
  (hg : ∀ i' _ : i' ∈ s, (g i').SupIndep f) : (s.bUnion g).SupIndep f :=
  by 
    rw [←sup_eq_bUnion]
    exact hs.sup hg

theorem sup_indep.pairwise_disjoint (hs : s.sup_indep f) : (s : Set ι).PairwiseDisjoint f :=
  fun a ha b hb hab => (hs ha).mono_right$ le_sup$ mem_erase.2 ⟨hab.symm, hb⟩

theorem sup_indep_iff_pairwise_disjoint : s.sup_indep f ↔ (s : Set ι).PairwiseDisjoint f :=
  by 
    refine' ⟨fun hs a ha b hb hab => (hs ha).mono_right$ le_sup$ mem_erase.2 ⟨hab.symm, hb⟩, fun hs a ha => _⟩
    rw [disjoint_sup_right]
    exact fun b hb => hs a ha b (mem_of_mem_erase hb) (ne_of_mem_erase hb).symm

alias sup_indep_iff_pairwise_disjoint ↔ Finset.SupIndep.pairwise_disjoint Set.PairwiseDisjoint.sup_indep

end Finset

theorem CompleteLattice.independent_iff_sup_indep [CompleteDistribLattice α] [DecidableEq ι] {s : Finset ι}
  {f : ι → α} : CompleteLattice.Independent (f ∘ (coeₓ : s → ι)) ↔ s.sup_indep f :=
  by 
    refine' subtype.forall.trans (forall_congrₓ$ fun a => forall_congrₓ$ fun b => _)
    rw [Finset.sup_eq_supr]
    congr 2
    refine' supr_subtype.trans _ 
    congr 1 with x 
    simp [supr_and, @supr_comm _ (x ∈ s)]

alias CompleteLattice.independent_iff_sup_indep ↔ CompleteLattice.Independent.sup_indep Finset.SupIndep.independent

