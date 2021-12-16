import Mathbin.Topology.Category.Top.Opens

/-!
# The category of open neighborhoods of a point

Given an object `X` of the category `Top` of topological spaces and a point `x : X`, this file
builds the type `open_nhds x` of open neighborhoods of `x` in `X` and endows it with the partial
order given by inclusion and the corresponding category structure (as a full subcategory of the
poset category `set X`). This is used in `topology.sheaves.stalks` to build the stalk of a sheaf
at `x` as a limit over `open_nhds x`.

## Main declarations

Besides `open_nhds`, the main constructions here are:

* `inclusion (x : X)`: the obvious functor `open_nhds x ⥤ opens X`
* `functor_nhds`: An open map `f : X ⟶ Y` induces a functor `open_nhds x ⥤ open_nhds (f x)`
* `adjunction_nhds`: An open map `f : X ⟶ Y` induces an adjunction between `open_nhds x` and
                     `open_nhds (f x)`.
-/


open CategoryTheory

open TopologicalSpace

open Opposite

universe u

variable {X Y : Top.{u}} (f : X ⟶ Y)

namespace TopologicalSpace

/-- The type of open neighbourhoods of a point `x` in a (bundled) topological space. -/
def open_nhds (x : X) :=
  { U : opens X // x ∈ U }

namespace OpenNhds

instance (x : X) : PartialOrderₓ (open_nhds x) :=
  { le := fun U V => U.1 ≤ V.1, le_refl := fun _ => le_reflₓ _, le_trans := fun _ _ _ => le_transₓ,
    le_antisymm := fun _ _ i j => Subtype.eq$ le_antisymmₓ i j }

instance (x : X) : Lattice (open_nhds x) :=
  { open_nhds.partial_order x with inf := fun U V => ⟨U.1⊓V.1, ⟨U.2, V.2⟩⟩,
    le_inf := fun U V W => @le_inf _ _ U.1.1 V.1.1 W.1.1, inf_le_left := fun U V => @inf_le_left _ _ U.1.1 V.1.1,
    inf_le_right := fun U V => @inf_le_right _ _ U.1.1 V.1.1, sup := fun U V => ⟨U.1⊔V.1, V.1.1.mem_union_left U.2⟩,
    sup_le := fun U V W => @sup_le _ _ U.1.1 V.1.1 W.1.1, le_sup_left := fun U V => @le_sup_left _ _ U.1.1 V.1.1,
    le_sup_right := fun U V => @le_sup_right _ _ U.1.1 V.1.1 }

instance (x : X) : OrderTop (open_nhds x) :=
  { top := ⟨⊤, trivialₓ⟩, le_top := fun _ => le_top }

instance (x : X) : Inhabited (open_nhds x) :=
  ⟨⊤⟩

instance open_nhds_category (x : X) : category.{u} (open_nhds x) :=
  by 
    unfold open_nhds 
    infer_instance

instance opens_nhds_hom_has_coe_to_fun {x : X} {U V : open_nhds x} : CoeFun (U ⟶ V) fun _ => U.1 → V.1 :=
  ⟨fun f x => ⟨x, f.le x.2⟩⟩

/--
The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets.
-/
def inf_le_left {x : X} (U V : open_nhds x) : U⊓V ⟶ U :=
  hom_of_le inf_le_left

/--
The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets.
-/
def inf_le_right {x : X} (U V : open_nhds x) : U⊓V ⟶ V :=
  hom_of_le inf_le_right

/-- The inclusion functor from open neighbourhoods of `x`
to open sets in the ambient topological space. -/
def inclusion (x : X) : open_nhds x ⥤ opens X :=
  full_subcategory_inclusion _

@[simp]
theorem inclusion_obj (x : X) U p : (inclusion x).obj ⟨U, p⟩ = U :=
  rfl

theorem OpenEmbedding {x : X} (U : open_nhds x) : OpenEmbedding U.1.inclusion :=
  U.1.OpenEmbedding

def map (x : X) : open_nhds (f x) ⥤ open_nhds x :=
  { obj :=
      fun U =>
        ⟨(opens.map f).obj U.1,
          by 
            tidy⟩,
    map := fun U V i => (opens.map f).map i }

@[simp]
theorem map_obj (x : X) U q :
  (map f x).obj ⟨U, q⟩ =
    ⟨(opens.map f).obj U,
      by 
        tidy⟩ :=
  rfl

@[simp]
theorem map_id_obj (x : X) U : (map (𝟙 X) x).obj U = U :=
  by 
    tidy

@[simp]
theorem map_id_obj' (x : X) U p q : (map (𝟙 X) x).obj ⟨⟨U, p⟩, q⟩ = ⟨⟨U, p⟩, q⟩ :=
  rfl

@[simp]
theorem map_id_obj_unop (x : X) (U : open_nhds xᵒᵖ) : (map (𝟙 X) x).obj (unop U) = unop U :=
  by 
    simp 

@[simp]
theorem op_map_id_obj (x : X) (U : open_nhds xᵒᵖ) : (map (𝟙 X) x).op.obj U = U :=
  by 
    simp 

/-- `opens.map f` and `open_nhds.map f` form a commuting square (up to natural isomorphism)
with the inclusion functors into `opens X`. -/
def inclusion_map_iso (x : X) : inclusion (f x) ⋙ opens.map f ≅ map f x ⋙ inclusion x :=
  nat_iso.of_components
    (fun U =>
      by 
        constructor 
        exact 𝟙 _ 
        exact 𝟙 _)
    (by 
      tidy)

@[simp]
theorem inclusion_map_iso_hom (x : X) : (inclusion_map_iso f x).hom = 𝟙 _ :=
  rfl

@[simp]
theorem inclusion_map_iso_inv (x : X) : (inclusion_map_iso f x).inv = 𝟙 _ :=
  rfl

end OpenNhds

end TopologicalSpace

namespace IsOpenMap

open TopologicalSpace

variable {f}

/--
An open map `f : X ⟶ Y` induces a functor `open_nhds x ⥤ open_nhds (f x)`.
-/
@[simps]
def functor_nhds (h : IsOpenMap f) (x : X) : open_nhds x ⥤ open_nhds (f x) :=
  { obj := fun U => ⟨h.functor.obj U.1, ⟨x, U.2, rfl⟩⟩, map := fun U V i => h.functor.map i }

/--
An open map `f : X ⟶ Y` induces an adjunction between `open_nhds x` and `open_nhds (f x)`.
-/
def adjunction_nhds (h : IsOpenMap f) (x : X) : IsOpenMap.functorNhds h x ⊣ open_nhds.map f x :=
  adjunction.mk_of_unit_counit
    { Unit := { app := fun U => hom_of_le$ fun x hxU => ⟨x, hxU, rfl⟩ },
      counit := { app := fun V => hom_of_le$ fun y ⟨x, hfxV, hxy⟩ => hxy ▸ hfxV } }

end IsOpenMap

