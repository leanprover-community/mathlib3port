import Mathbin.CategoryTheory.Subobject.WellPowered 
import Mathbin.CategoryTheory.Types

/-!
# `Type u` is well-powered

By building a categorical equivalence `mono_over α ≌ set α` for any `α : Type u`,
we deduce that `subobject α ≃o set α` and that `Type u` is well-powered.

One would hope that for a particular concrete category `C` (`AddCommGroup`, etc)
it's viable to prove `[well_powered C]` without explicitly aligning `subobject X`
with the "hand-rolled" definition of subobjects.

This may be possible using Lawvere theories,
but it remains to be seen whether this just pushes lumps around in the carpet.
-/


universe u

open CategoryTheory

open CategoryTheory.Subobject

open_locale CategoryTheory.Type

theorem subtype_val_mono {α : Type u} (s : Set α) : mono (↾(Subtype.val : s → α)) :=
  (mono_iff_injective _).mpr Subtype.val_injective

attribute [local instance] subtype_val_mono

/--
The category of `mono_over α`, for `α : Type u`, is equivalent to the partial order `set α`.
-/
@[simps]
noncomputable def Types.monoOverEquivalenceSet (α : Type u) : mono_over α ≌ Set α :=
  { Functor :=
      { obj := fun f => Set.Range f.1.Hom,
        map :=
          fun f g t =>
            hom_of_le
              (by 
                rintro a ⟨x, rfl⟩
                exact ⟨t.1 x, congr_funₓ t.w x⟩) },
    inverse :=
      { obj := fun s => mono_over.mk' (Subtype.val : s → α),
        map :=
          fun s t b =>
            mono_over.hom_mk (fun w => ⟨w.1, Set.mem_of_mem_of_subset w.2 b.le⟩)
              (by 
                ext 
                simp ) },
    unitIso :=
      nat_iso.of_components
        (fun f =>
          mono_over.iso_mk (Equivₓ.ofInjective f.1.Hom ((mono_iff_injective _).mp f.2)).toIso
            (by 
              tidy))
        (by 
          tidy),
    counitIso :=
      nat_iso.of_components (fun s => eq_to_iso Subtype.range_val)
        (by 
          tidy) }

instance : well_powered (Type u) :=
  well_powered_of_essentially_small_mono_over fun α => essentially_small.mk' (Types.monoOverEquivalenceSet α)

/--
For `α : Type u`, `subobject α` is order isomorphic to `set α`.
-/
noncomputable def Types.subobjectEquivSet (α : Type u) : subobject α ≃o Set α :=
  (Types.monoOverEquivalenceSet α).thinSkeletonOrderIso

