import Mathbin.CategoryTheory.Subobject.Basic 
import Mathbin.CategoryTheory.EssentiallySmall

/-!
# Well-powered categories

A category `(C : Type u) [category.{v} C]` is `[well_powered C]` if
for every `X : C`, we have `small.{v} (subobject X)`.

(Note that in this situtation `subobject X : Type (max u v)`,
so this is a nontrivial condition for large categories,
but automatic for small categories.)

This is equivalent to the category `mono_over X` being `essentially_small.{v}` for all `X : C`.

When a category is well-powered, you can obtain nonconstructive witnesses as
`shrink (subobject X) : Type v`
and
`equiv_shrink (subobject X) : subobject X ≃ shrink (subobject X)`.
-/


universe v u₁ u₂

namespace CategoryTheory

variable(C : Type u₁)[category.{v} C]

/--
A category (with morphisms in `Type v`) is well-powered if `subobject X` is `v`-small for every `X`.

We show in `well_powered_of_mono_over_essentially_small` and `mono_over_essentially_small`
that this is the case if and only if `mono_over X` is `v`-essentially small for every `X`.
-/
class well_powered : Prop where 
  subobject_small : ∀ X : C, Small.{v} (subobject X) :=  by 
  runTac 
    tactic.apply_instance

instance small_subobject [well_powered C] (X : C) : Small.{v} (subobject X) :=
  well_powered.subobject_small X

instance (priority := 100)well_powered_of_small_category (C : Type u₁) [small_category C] : well_powered C :=
  {  }

variable{C}

theorem essentially_small_mono_over_iff_small_subobject (X : C) :
  essentially_small.{v} (mono_over X) ↔ Small.{v} (subobject X) :=
  essentially_small_iff_of_thin

theorem well_powered_of_essentially_small_mono_over (h : ∀ X : C, essentially_small.{v} (mono_over X)) :
  well_powered C :=
  { subobject_small := fun X => (essentially_small_mono_over_iff_small_subobject X).mp (h X) }

section 

variable[well_powered C]

instance essentially_small_mono_over (X : C) : essentially_small.{v} (mono_over X) :=
  (essentially_small_mono_over_iff_small_subobject X).mpr (well_powered.subobject_small X)

end 

section Equivalenceₓ

variable{D : Type u₂}[category.{v} D]

theorem well_powered_of_equiv (e : C ≌ D) [well_powered C] : well_powered D :=
  well_powered_of_essentially_small_mono_over$
    fun X =>
      (essentially_small_congr (mono_over.congr X e.symm)).2$
        by 
          infer_instance

/-- Being well-powered is preserved by equivalences, as long as the two categories involved have
    their morphisms in the same universe. -/
theorem well_powered_congr (e : C ≌ D) : well_powered C ↔ well_powered D :=
  ⟨fun i =>
      by 
        exact well_powered_of_equiv e,
    fun i =>
      by 
        exact well_powered_of_equiv e.symm⟩

end Equivalenceₓ

end CategoryTheory

