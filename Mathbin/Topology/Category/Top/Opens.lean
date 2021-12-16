import Mathbin.Topology.Opens 
import Mathbin.CategoryTheory.Category.Preorder 
import Mathbin.CategoryTheory.EqToHom 
import Mathbin.Topology.Category.Top.EpiMono

/-!
# The category of open sets in a topological space.

We define `to_Top : opens X ⥤ Top` and
`map (f : X ⟶ Y) : opens Y ⥤ opens X`, given by taking preimages of open sets.

Unfortunately `opens` isn't (usefully) a functor `Top ⥤ Cat`.
(One can in fact define such a functor,
but using it results in unresolvable `eq.rec` terms in goals.)

Really it's a 2-functor from (spaces, continuous functions, equalities)
to (categories, functors, natural isomorphisms).
We don't attempt to set up the full theory here, but do provide the natural isomorphisms
`map_id : map (𝟙 X) ≅ 𝟭 (opens X)` and
`map_comp : map (f ≫ g) ≅ map g ⋙ map f`.

Beyond that, there's a collection of simp lemmas for working with these constructions.
-/


open CategoryTheory

open TopologicalSpace

open Opposite

universe u

namespace TopologicalSpace.Opens

variable {X Y Z : Top.{u}}

/-!
Since `opens X` has a partial order, it automatically receives a `category` instance.
Unfortunately, because we do not allow morphisms in `Prop`,
the morphisms `U ⟶ V` are not just proofs `U ≤ V`, but rather
`ulift (plift (U ≤ V))`.
-/


instance opens_hom_has_coe_to_fun {U V : opens X} : CoeFun (U ⟶ V) fun f => U → V :=
  ⟨fun f x => ⟨x, f.le x.2⟩⟩

/-!
We now construct as morphisms various inclusions of open sets.
-/


/--
The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets.
-/
def inf_le_left (U V : opens X) : U⊓V ⟶ U :=
  inf_le_left.hom

/--
The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets.
-/
def inf_le_right (U V : opens X) : U⊓V ⟶ V :=
  inf_le_right.hom

/--
The inclusion `U i ⟶ supr U` as a morphism in the category of open sets.
-/
def le_supr {ι : Type _} (U : ι → opens X) (i : ι) : U i ⟶ supr U :=
  (le_supr U i).hom

/--
The inclusion `⊥ ⟶ U` as a morphism in the category of open sets.
-/
def bot_le (U : opens X) : ⊥ ⟶ U :=
  bot_le.hom

/--
The inclusion `U ⟶ ⊤` as a morphism in the category of open sets.
-/
def le_top (U : opens X) : U ⟶ ⊤ :=
  le_top.hom

theorem inf_le_left_apply (U V : opens X) x : (inf_le_left U V) x = ⟨x.1, (@_root_.inf_le_left _ _ U V : _ ≤ _) x.2⟩ :=
  rfl

@[simp]
theorem inf_le_left_apply_mk (U V : opens X) x m :
  (inf_le_left U V) ⟨x, m⟩ = ⟨x, (@_root_.inf_le_left _ _ U V : _ ≤ _) m⟩ :=
  rfl

@[simp]
theorem le_supr_apply_mk {ι : Type _} (U : ι → opens X) (i : ι) x m :
  (le_supr U i) ⟨x, m⟩ = ⟨x, (_root_.le_supr U i : _) m⟩ :=
  rfl

/--
The functor from open sets in `X` to `Top`,
realising each open set as a topological space itself.
-/
def to_Top (X : Top.{u}) : opens X ⥤ Top :=
  { obj := fun U => ⟨U.val, inferInstance⟩,
    map :=
      fun U V i =>
        ⟨fun x => ⟨x.1, i.le x.2⟩, (Embedding.continuous_iff embedding_subtype_coe).2 continuous_induced_dom⟩ }

@[simp]
theorem to_Top_map (X : Top.{u}) {U V : opens X} {f : U ⟶ V} {x} {h} : ((to_Top X).map f) ⟨x, h⟩ = ⟨x, f.le h⟩ :=
  rfl

/--
The inclusion map from an open subset to the whole space, as a morphism in `Top`.
-/
@[simps]
def inclusion {X : Top.{u}} (U : opens X) : (to_Top X).obj U ⟶ X :=
  { toFun := _, continuous_to_fun := continuous_subtype_coe }

theorem OpenEmbedding {X : Top.{u}} (U : opens X) : OpenEmbedding (inclusion U) :=
  IsOpen.open_embedding_subtype_coe U.2

/--
The inclusion of the top open subset (i.e. the whole space) is an isomorphism.
-/
def inclusion_top_iso (X : Top.{u}) : (to_Top X).obj ⊤ ≅ X :=
  { hom := inclusion ⊤, inv := ⟨fun x => ⟨x, trivialₓ⟩, continuous_def.2$ fun U ⟨S, hS, hSU⟩ => hSU ▸ hS⟩ }

/-- `opens.map f` gives the functor from open sets in Y to open set in X,
    given by taking preimages under f. -/
def map (f : X ⟶ Y) : opens Y ⥤ opens X :=
  { obj := fun U => ⟨f ⁻¹' U.val, U.property.preimage f.continuous⟩, map := fun U V i => ⟨⟨fun x h => i.le h⟩⟩ }

@[simp]
theorem map_obj (f : X ⟶ Y) U p : (map f).obj ⟨U, p⟩ = ⟨f ⁻¹' U, p.preimage f.continuous⟩ :=
  rfl

@[simp]
theorem map_id_obj (U : opens X) : (map (𝟙 X)).obj U = U :=
  let ⟨_, _⟩ := U 
  rfl

@[simp]
theorem map_id_obj' U p : (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩ :=
  rfl

@[simp]
theorem map_id_obj_unop (U : opens Xᵒᵖ) : (map (𝟙 X)).obj (unop U) = unop U :=
  let ⟨_, _⟩ := U.unop 
  rfl

@[simp]
theorem op_map_id_obj (U : opens Xᵒᵖ) : (map (𝟙 X)).op.obj U = U :=
  by 
    simp 

/--
The inclusion `U ⟶ (map f).obj ⊤` as a morphism in the category of open sets.
-/
def le_map_top (f : X ⟶ Y) (U : opens X) : U ⟶ (map f).obj ⊤ :=
  le_top U

@[simp]
theorem map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) U : (map (f ≫ g)).obj U = (map f).obj ((map g).obj U) :=
  rfl

@[simp]
theorem map_comp_obj' (f : X ⟶ Y) (g : Y ⟶ Z) U p : (map (f ≫ g)).obj ⟨U, p⟩ = (map f).obj ((map g).obj ⟨U, p⟩) :=
  rfl

@[simp]
theorem map_comp_map (f : X ⟶ Y) (g : Y ⟶ Z) {U V} (i : U ⟶ V) : (map (f ≫ g)).map i = (map f).map ((map g).map i) :=
  rfl

@[simp]
theorem map_comp_obj_unop (f : X ⟶ Y) (g : Y ⟶ Z) U : (map (f ≫ g)).obj (unop U) = (map f).obj ((map g).obj (unop U)) :=
  rfl

@[simp]
theorem op_map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) U : (map (f ≫ g)).op.obj U = (map f).op.obj ((map g).op.obj U) :=
  rfl

theorem map_supr (f : X ⟶ Y) {ι : Type _} (U : ι → opens Y) : (map f).obj (supr U) = supr ((map f).obj ∘ U) :=
  by 
    apply Subtype.eq 
    rw [supr_def, supr_def, map_obj]
    dsimp 
    rw [Set.preimage_Union]
    rfl

section 

variable (X)

/--
The functor `opens X ⥤ opens X` given by taking preimages under the identity function
is naturally isomorphic to the identity functor.
-/
@[simps]
def map_id : map (𝟙 X) ≅ 𝟭 (opens X) :=
  { hom := { app := fun U => eq_to_hom (map_id_obj U) }, inv := { app := fun U => eq_to_hom (map_id_obj U).symm } }

theorem map_id_eq : map (𝟙 X) = 𝟭 (opens X) :=
  by 
    unfold map 
    congr 
    ext 
    rfl 
    ext

end 

/--
The natural isomorphism between taking preimages under `f ≫ g`, and the composite
of taking preimages under `g`, then preimages under `f`.
-/
@[simps]
def map_comp (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f :=
  { hom := { app := fun U => eq_to_hom (map_comp_obj f g U) },
    inv := { app := fun U => eq_to_hom (map_comp_obj f g U).symm } }

theorem map_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map g ⋙ map f :=
  rfl

/--
If two continuous maps `f g : X ⟶ Y` are equal,
then the functors `opens Y ⥤ opens X` they induce are isomorphic.
-/
def map_iso (f g : X ⟶ Y) (h : f = g) : map f ≅ map g :=
  nat_iso.of_components (fun U => eq_to_iso (congr_funₓ (congr_argₓ functor.obj (congr_argₓ map h)) U))
    (by 
      runTac 
        obviously)

theorem map_eq (f g : X ⟶ Y) (h : f = g) : map f = map g :=
  by 
    unfold map 
    congr 
    ext 
    rw [h]
    rw [h]
    assumption'

@[simp]
theorem map_iso_refl (f : X ⟶ Y) h : map_iso f f h = iso.refl (map _) :=
  rfl

@[simp]
theorem map_iso_hom_app (f g : X ⟶ Y) (h : f = g) (U : opens Y) :
  (map_iso f g h).hom.app U = eq_to_hom (congr_funₓ (congr_argₓ functor.obj (congr_argₓ map h)) U) :=
  rfl

@[simp]
theorem map_iso_inv_app (f g : X ⟶ Y) (h : f = g) (U : opens Y) :
  (map_iso f g h).inv.app U = eq_to_hom (congr_funₓ (congr_argₓ functor.obj (congr_argₓ map h.symm)) U) :=
  rfl

/-- A homeomorphism of spaces gives an equivalence of categories of open sets. -/
@[simps]
def map_map_iso {X Y : Top.{u}} (H : X ≅ Y) : opens Y ≌ opens X :=
  { Functor := map H.hom, inverse := map H.inv,
    unitIso :=
      nat_iso.of_components
        (fun U =>
          eq_to_iso
            (by 
              simp [map, Set.preimage_preimage]))
        (by 
          intro _ _ _ 
          simp ),
    counitIso :=
      nat_iso.of_components
        (fun U =>
          eq_to_iso
            (by 
              simp [map, Set.preimage_preimage]))
        (by 
          intro _ _ _ 
          simp ) }

end TopologicalSpace.Opens

/--
An open map `f : X ⟶ Y` induces a functor `opens X ⥤ opens Y`.
-/
@[simps]
def IsOpenMap.functor {X Y : Top} {f : X ⟶ Y} (hf : IsOpenMap f) : opens X ⥤ opens Y :=
  { obj := fun U => ⟨f '' U, hf U U.2⟩, map := fun U V h => ⟨⟨Set.image_subset _ h.down.down⟩⟩ }

/--
An open map `f : X ⟶ Y` induces an adjunction between `opens X` and `opens Y`.
-/
def IsOpenMap.adjunction {X Y : Top} {f : X ⟶ Y} (hf : IsOpenMap f) :
  adjunction hf.functor (TopologicalSpace.Opens.map f) :=
  adjunction.mk_of_unit_counit
    { Unit := { app := fun U => hom_of_le$ fun x hxU => ⟨x, hxU, rfl⟩ },
      counit := { app := fun V => hom_of_le$ fun y ⟨x, hfxV, hxy⟩ => hxy ▸ hfxV } }

instance IsOpenMap.functorFullOfMono {X Y : Top} {f : X ⟶ Y} (hf : IsOpenMap f) [H : mono f] : full hf.functor :=
  { Preimage :=
      fun U V i =>
        hom_of_le
          fun x hx =>
            by 
              obtain ⟨y, hy, eq⟩ := i.le ⟨x, hx, rfl⟩
              exact (Top.mono_iff_injective f).mp H Eq ▸ hy }

instance IsOpenMap.functor_faithful {X Y : Top} {f : X ⟶ Y} (hf : IsOpenMap f) : faithful hf.functor :=
  {  }

namespace TopologicalSpace.Opens

open TopologicalSpace

theorem inclusion_top_functor (X : Top) :
  (@opens.open_embedding X ⊤).IsOpenMap.Functor = map (inclusion_top_iso X).inv :=
  by 
    apply functor.hext 
    intro 
    abstract obj_eq 
      ext 
      exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨x, trivialₓ⟩, h, rfl⟩⟩
    intros 
    apply Subsingleton.helimₓ 
    congr 1
    iterate 2 
      apply inclusion_top_functor.obj_eq

end TopologicalSpace.Opens

