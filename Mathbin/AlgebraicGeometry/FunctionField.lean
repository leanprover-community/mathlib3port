import Mathbin.AlgebraicGeometry.Properties

/-!
# Function field of integral schemes

We define the function field of an irreducible scheme as the stalk of the generic point.
This is a field when the scheme is integral.

## Main definition
* `algebraic_geometry.Scheme.function_field`: The function field of an integral scheme.
* `algebraic_geometry.germ_to_function_field`: The canonical map from a component into the function
  field. This map is injective.
-/


universe u v

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits Top

namespace AlgebraicGeometry

variable (X : Scheme)

/-- The function field of an irreducible scheme is the local ring at its generic point.
Despite the name, this is a field only when the scheme is integral. -/
noncomputable abbrev Scheme.function_field [IrreducibleSpace X.carrier] : CommRingₓₓ :=
  X.presheaf.stalk (genericPoint X.carrier)

/-- The restriction map from a component to the function field. -/
noncomputable abbrev Scheme.germ_to_function_field [IrreducibleSpace X.carrier] (U : opens X.carrier) [h : Nonempty U] :
    X.presheaf.obj (op U) ⟶ X.function_field :=
  X.presheaf.germ
    ⟨genericPoint X.carrier,
      ((generic_point_spec X.carrier).mem_open_set_iff U.prop).mpr
        (by
          simpa using h)⟩

noncomputable instance [IsIntegral X] : Field X.function_field := by
  apply fieldOfIsUnitOrEqZero
  intro a
  obtain ⟨U, m, s, rfl⟩ := Top.Presheaf.germ_exist _ _ a
  rw [or_iff_not_imp_right, ← (X.presheaf.germ ⟨_, m⟩).map_zero]
  intro ha
  replace ha := ne_of_apply_ne _ ha
  have hs : genericPoint X.carrier ∈ RingedSpace.basic_open _ s := by
    rw [← opens.mem_coe, (generic_point_spec X.carrier).mem_open_set_iff, Set.top_eq_univ, Set.univ_inter, ←
      Set.ne_empty_iff_nonempty, Ne.def, ← opens.coe_bot, subtype.coe_injective.eq_iff, ← opens.empty_eq]
    erw [basic_open_eq_bot_iff]
    exacts[ha, (RingedSpace.basic_open _ _).Prop]
  have := (X.presheaf.germ ⟨_, hs⟩).is_unit_map (RingedSpace.is_unit_res_basic_open _ s)
  rwa [Top.Presheaf.germ_res_apply] at this

theorem germ_injective_of_is_integral [IsIntegral X] {U : opens X.carrier} (x : U) :
    Function.Injective (X.presheaf.germ x) := by
  rw [RingHom.injective_iff]
  intro y hy
  rw [← (X.presheaf.germ x).map_zero] at hy
  obtain ⟨W, hW, iU, iV, e⟩ := X.presheaf.germ_eq _ x.prop x.prop _ _ hy
  cases show iU = iV from Subsingleton.elimₓ _ _
  have : Nonempty W := ⟨⟨_, hW⟩⟩
  exact map_injective_of_is_integral X iU e

theorem Scheme.germ_to_function_field_injective [IsIntegral X] (U : opens X.carrier) [Nonempty U] :
    Function.Injective (X.germ_to_function_field U) :=
  germ_injective_of_is_integral _ _

end AlgebraicGeometry

