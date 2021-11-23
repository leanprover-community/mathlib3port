import Mathbin.CategoryTheory.Sites.Spaces 
import Mathbin.Topology.Sheaves.Sheaf 
import Mathbin.CategoryTheory.Sites.DenseSubsite

/-!

# The sheaf condition in terms of sites.

The theory of sheaves on sites is developed independently from sheaves on spaces in
`category_theory/sites`. In this file, we connect the two theories: We show that for a topological
space `X`, a presheaf `F : (opens X)ᵒᵖ ⥤ C` is a sheaf on the site `opens X` if and only if it is
a sheaf on `X` in the usual sense.

Recall that a presheaf `F : (opens X)ᵒᵖ ⥤ C` is called a *sheaf* on the space `X`, if for every
family of opens `U : ι → opens X`, the object `F.obj (op (supr U))` is the limit of some fork
diagram. On the other hand, `F` is called a *sheaf* on the site `opens X`, if for every open set
`U : opens X` and every presieve `R : presieve U`, the object `F.obj (op U)` is the limit of a
very similar fork diagram. In this file, we will construct the two functions `covering_of_presieve`
and `presieve_of_covering`, which translate between the two concepts. We then prove a bunch of
naturality lemmas relating the two fork diagrams to each other.

## Main statements
* `is_sheaf_sites_iff_is_sheaf_spaces`. A presheaf `F : (opens X)ᵒᵖ ⥤ C` is a sheaf on the site
  `opens X` if and only if it is a sheaf on the space `X`.
* `Sheaf_sites_eq_sheaf_spaces`. The type of sheaves on the site `opens X` is *equal* to the type
  of sheaves on the space `X`.

-/


noncomputable theory

universe u v w

namespace Top.Presheaf

open CategoryTheory TopologicalSpace Top CategoryTheory.Limits Opposite

open Top.Presheaf.SheafConditionEqualizerProducts

variable{C : Type u}[category.{v} C][has_products C]

variable{X : Top.{v}}(F : presheaf C X)

/--
Given a presieve `R` on `U`, we obtain a covering family of open sets in `X`, by taking as index
type the type of dependent pairs `(V, f)`, where `f : V ⟶ U` is in `R`.
-/
def covering_of_presieve (U : opens X) (R : presieve U) : (ΣV, { f : V ⟶ U // R f }) → opens X :=
  fun f => f.1

@[simp]
theorem covering_of_presieve_apply (U : opens X) (R : presieve U) (f : ΣV, { f : V ⟶ U // R f }) :
  covering_of_presieve U R f = f.1 :=
  rfl

namespace CoveringOfPresieve

variable(U : opens X)(R : presieve U)

/-!
In this section, we will relate two different fork diagrams to each other.

The first one is the defining fork diagram for the sheaf condition in terms of sites, applied to
the presieve `R`. It will henceforth be called the _sites diagram_. Its objects are called
`presheaf.first_obj` and `presheaf.second_obj` and its morphisms are `presheaf.first_map` and
`presheaf.second_obj`. The fork map into this diagram is called `presheaf.fork_map`.

The second one is the defining fork diagram for the sheaf condition in terms of spaces, applied to
the family of opens `covering_of_presieve U R`. It will henceforth be called the _spaces diagram_.
Its objects are called `pi_opens` and `pi_inters` and its morphisms are `left_res` and `right_res`.
The fork map into this diagram is called `res`.

-/


/--
If `R` is a presieve in the grothendieck topology on `opens X`, the covering family associated to
`R` really is _covering_, i.e. the union of all open sets equals `U`.
-/
theorem supr_eq_of_mem_grothendieck (hR : sieve.generate R ∈ Opens.grothendieckTopology X U) :
  supr (covering_of_presieve U R) = U :=
  by 
    apply le_antisymmₓ
    ·
      refine' supr_le _ 
      intro f 
      exact f.2.1.le 
    intro x hxU 
    rw [opens.mem_coe, opens.mem_supr]
    obtain ⟨V, iVU, ⟨W, iVW, iWU, hiWU, -⟩, hxV⟩ := hR x hxU 
    exact ⟨⟨W, ⟨iWU, hiWU⟩⟩, iVW.le hxV⟩

/--
The first object in the sites diagram is isomorphic to the first object in the spaces diagram.
Actually, they are even definitionally equal, but it is convenient to give this isomorphism a name.
-/
def first_obj_iso_pi_opens : presheaf.first_obj R F ≅ pi_opens F (covering_of_presieve U R) :=
  eq_to_iso rfl

/--
The isomorphism `first_obj_iso_pi_opens` is compatible with canonical projections out of the
product.
-/
theorem first_obj_iso_pi_opens_π (f : ΣV, { f : V ⟶ U // R f }) :
  (first_obj_iso_pi_opens F U R).hom ≫ pi.π _ f = pi.π _ f :=
  category.id_comp _

/--
The second object in the sites diagram is isomorphic to the second object in the spaces diagram.
-/
def second_obj_iso_pi_inters : presheaf.second_obj R F ≅ pi_inters F (covering_of_presieve U R) :=
  has_limit.iso_of_nat_iso$
    discrete.nat_iso$ fun i => F.map_iso (eq_to_iso (complete_lattice.pullback_eq_inf _ _).symm).op

/--
The isomorphism `second_obj_iso_pi_inters` is compatible with canonical projections out of the
product. Here, we have to insert an `eq_to_hom` arrow to pass from
`F.obj (op (pullback f.2.1 g.2.1))` to `F.obj (op (f.1 ⊓ g.1))`.
-/
theorem second_obj_iso_pi_inters_π (f g : ΣV, { f : V ⟶ U // R f }) :
  (second_obj_iso_pi_inters F U R).hom ≫ pi.π _ (f, g) =
    pi.π _ (f, g) ≫ F.map (eq_to_hom (complete_lattice.pullback_eq_inf f.2.1 g.2.1).symm).op :=
  by 
    dunfold second_obj_iso_pi_inters 
    rw [has_limit.iso_of_nat_iso_hom_π]
    rfl

/--
Composing the fork map of the sites diagram with the isomorphism `first_obj_iso_pi_opens` is the
same as the fork map of the spaces diagram (modulo an `eq_to_hom` arrow).
-/
theorem fork_map_comp_first_obj_iso_pi_opens_eq (hR : sieve.generate R ∈ Opens.grothendieckTopology X U) :
  presheaf.fork_map R F ≫ (first_obj_iso_pi_opens F U R).hom =
    F.map (eq_to_hom (supr_eq_of_mem_grothendieck U R hR)).op ≫ res F (covering_of_presieve U R) :=
  by 
    ext f 
    rw [category.assoc, category.assoc]
    rw [first_obj_iso_pi_opens_π]
    dunfold presheaf.fork_map res 
    rw [limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, ←F.map_comp]
    congr

/--
First naturality condition. Under the isomorphisms `first_obj_iso_pi_opens` and
`second_obj_iso_pi_inters`, the map `presheaf.first_map` corresponds to `left_res`.
-/
theorem first_obj_iso_comp_left_res_eq :
  presheaf.first_map R F ≫ (second_obj_iso_pi_inters F U R).hom =
    (first_obj_iso_pi_opens F U R).hom ≫ left_res F (covering_of_presieve U R) :=
  by 
    ext ⟨f, g⟩
    rw [category.assoc, category.assoc, second_obj_iso_pi_inters_π]
    dunfold left_res presheaf.first_map 
    rw [limit.lift_π, fan.mk_π_app, limit.lift_π_assoc, fan.mk_π_app, ←category.assoc]
    erw [first_obj_iso_pi_opens_π, category.assoc, ←F.map_comp]
    rfl

/--
Second naturality condition. Under the isomorphisms `first_obj_iso_pi_opens` and
`second_obj_iso_pi_inters`, the map `presheaf.second_map` corresponds to `right_res`.
-/
theorem first_obj_iso_comp_right_res_eq :
  presheaf.second_map R F ≫ (second_obj_iso_pi_inters F U R).hom =
    (first_obj_iso_pi_opens F U R).hom ≫ right_res F (covering_of_presieve U R) :=
  by 
    ext ⟨f, g⟩
    dunfold right_res presheaf.second_map 
    rw [category.assoc, category.assoc, second_obj_iso_pi_inters_π, limit.lift_π, fan.mk_π_app, limit.lift_π_assoc,
      fan.mk_π_app, ←category.assoc, first_obj_iso_pi_opens_π, category.assoc, ←F.map_comp]
    rfl

/-- The natural isomorphism between the sites diagram and the spaces diagram. -/
@[simps]
def diagram_nat_iso :
  parallel_pair (presheaf.first_map R F) (presheaf.second_map R F) ≅ diagram F (covering_of_presieve U R) :=
  (nat_iso.of_components
      fun i => walking_parallel_pair.cases_on i (first_obj_iso_pi_opens F U R) (second_obj_iso_pi_inters F U R))$
    by 
      intro i j f 
      cases i
      ·
        cases j
        ·
          cases f 
          simp 
        ·
          cases f
          ·
            exact first_obj_iso_comp_left_res_eq F U R
          ·
            exact first_obj_iso_comp_right_res_eq F U R
      ·
        cases j
        ·
          cases f
        ·
          cases f 
          simp 

/--
Postcomposing the given fork of the _sites_ diagram with the natural isomorphism between the
diagrams gives us a fork of the _spaces_ diagram. We construct a morphism from this fork to the
given fork of the _spaces_ diagram. This is shown to be an isomorphism below.
-/
@[simps]
def postcompose_diagram_fork_hom (hR : sieve.generate R ∈ Opens.grothendieckTopology X U) :
  (cones.postcompose (diagram_nat_iso F U R).hom).obj (fork.of_ι _ (presheaf.w R F)) ⟶
    fork F (covering_of_presieve U R) :=
  fork.mk_hom (F.map (eq_to_hom (supr_eq_of_mem_grothendieck U R hR)).op)
    (fork_map_comp_first_obj_iso_pi_opens_eq F U R hR).symm

instance is_iso_postcompose_diagram_fork_hom_hom (hR : sieve.generate R ∈ Opens.grothendieckTopology X U) :
  is_iso (postcompose_diagram_fork_hom F U R hR).hom :=
  by 
    rw [postcompose_diagram_fork_hom_hom]
    apply eq_to_hom.is_iso

instance is_iso_postcompose_diagram_fork_hom (hR : sieve.generate R ∈ Opens.grothendieckTopology X U) :
  is_iso (postcompose_diagram_fork_hom F U R hR) :=
  cones.cone_iso_of_hom_iso _

/-- See `postcompose_diagram_fork_hom`. -/
def postcompose_diagram_fork_iso (hR : sieve.generate R ∈ Opens.grothendieckTopology X U) :
  (cones.postcompose (diagram_nat_iso F U R).hom).obj (fork.of_ι _ (presheaf.w R F)) ≅
    fork F (covering_of_presieve U R) :=
  as_iso (postcompose_diagram_fork_hom F U R hR)

end CoveringOfPresieve

theorem is_sheaf_sites_of_is_sheaf_spaces (Fsh : F.is_sheaf) : presheaf.is_sheaf (Opens.grothendieckTopology X) F :=
  by 
    rw [presheaf.is_sheaf_iff_is_sheaf']
    intro U R hR 
    refine' ⟨_⟩
    apply (is_limit.of_cone_equiv (cones.postcompose_equivalence (covering_of_presieve.diagram_nat_iso F U R))).toFun 
    apply (is_limit.equiv_iso_limit (covering_of_presieve.postcompose_diagram_fork_iso F U R hR)).invFun 
    exact (Fsh (covering_of_presieve U R)).some

/--
Given a family of opens `U : ι → opens X`, we obtain a presieve on `supr U` by declaring that a
morphism `f : V ⟶ supr U` is a member of the presieve if and only if there exists an index `i : ι`
such that `V = U i`.
-/
def presieve_of_covering {ι : Type v} (U : ι → opens X) : presieve (supr U) :=
  fun V f => ∃ i, V = U i

namespace PresieveOfCovering

/-!
In this section, we will relate two different fork diagrams to each other.

The first one is the defining fork diagram for the sheaf condition in terms of spaces, applied to
the family of opens `U`. It will henceforth be called the _spaces diagram_. Its objects are called
`pi_opens` and `pi_inters` and its morphisms are `left_res` and `right_res`. The fork map into this
diagram is called `res`.

The second one is the defining fork diagram for the sheaf condition in terms of sites, applied to
the presieve `presieve_of_covering U`. It will henceforth be called the _sites diagram_. Its objects
are called `presheaf.first_obj` and `presheaf.second_obj` and its morphisms are `presheaf.first_map`
and `presheaf.second_obj`. The fork map into this diagram is called `presheaf.fork_map`.

-/


variable{ι : Type v}(U : ι → opens X)

/--
The sieve generated by `presieve_of_covering U` is a member of the grothendieck topology.
-/
theorem mem_grothendieck_topology : sieve.generate (presieve_of_covering U) ∈ Opens.grothendieckTopology X (supr U) :=
  by 
    intro x hx 
    obtain ⟨i, hxi⟩ := opens.mem_supr.mp hx 
    exact ⟨U i, opens.le_supr U i, ⟨U i, 𝟙 _, opens.le_supr U i, ⟨i, rfl⟩, category.id_comp _⟩, hxi⟩

/--
An index `i : ι` can be turned into a dependent pair `(V, f)`, where `V` is an open set and
`f : V ⟶ supr U` is a member of `presieve_of_covering U f`.
-/
def hom_of_index (i : ι) : ΣV, { f : V ⟶ supr U // presieve_of_covering U f } :=
  ⟨U i, opens.le_supr U i, i, rfl⟩

/--
By using the axiom of choice, a dependent pair `(V, f)` where `f : V ⟶ supr U` is a member of
`presieve_of_covering U f` can be turned into an index `i : ι`, such that `V = U i`.
-/
def index_of_hom (f : ΣV, { f : V ⟶ supr U // presieve_of_covering U f }) : ι :=
  f.2.2.some

theorem index_of_hom_spec (f : ΣV, { f : V ⟶ supr U // presieve_of_covering U f }) : f.1 = U (index_of_hom U f) :=
  f.2.2.some_spec

/--
The canonical morphism from the first object in the sites diagram to the first object in the
spaces diagram. Note that this is *not* an isomorphism, as the product `pi_opens F U` may contain
duplicate factors, i.e. `U : ι → opens X` may not be injective.
-/
def first_obj_to_pi_opens : presheaf.first_obj (presieve_of_covering U) F ⟶ pi_opens F U :=
  pi.lift fun i => pi.π _ (hom_of_index U i)

/--
The canonical morphism from the first object in the spaces diagram to the first object in the
sites diagram. Note that this is *not* an isomorphism, as the product `pi_opens F U` may contain
duplicate factors, i.e. `U : ι → opens X` may not be injective.
-/
def pi_opens_to_first_obj : pi_opens F U ⟶ presheaf.first_obj.{v, v, u} (presieve_of_covering U) F :=
  pi.lift fun f => pi.π _ (index_of_hom U f) ≫ F.map (eq_to_hom (index_of_hom_spec U f)).op

-- error in Topology.Sheaves.SheafCondition.Sites: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Even though `first_obj_to_pi_opens` and `pi_opens_to_first_obj` are not inverse to each other,
applying them both after a fork map `s.ι` does nothing. The intuition here is that a compatible
family `s : Π i : ι, F.obj (op (U i))` does not care about duplicate open sets:
If `U i = U j` the the compatible family coincides on the intersection `U i ⊓ U j = U i = U j`,
hence `s i = s j` (module an `eq_to_hom` arrow).
-/
theorem fork_ι_comp_pi_opens_to_first_obj_to_pi_opens_eq
(s : limits.fork (left_res F U) (right_res F U)) : «expr = »(«expr ≫ »(s.ι, «expr ≫ »(pi_opens_to_first_obj F U, first_obj_to_pi_opens F U)), s.ι) :=
begin
  ext [] [ident j] [],
  dunfold [ident first_obj_to_pi_opens, ident pi_opens_to_first_obj] [],
  rw ["[", expr category.assoc, ",", expr category.assoc, ",", expr limit.lift_π, ",", expr fan.mk_π_app, ",", expr limit.lift_π, ",", expr fan.mk_π_app, "]"] [],
  have [ident i_eq] [":", expr «expr ⟶ »(U j, «expr ⊓ »(U j, U (index_of_hom U (hom_of_index U j))))] [],
  { apply [expr eq_to_hom],
    rw ["<-", expr index_of_hom_spec U] [],
    exact [expr inf_idem.symm] },
  have [] [] [":=", expr congr_arg (λ
    f, «expr ≫ »(f, «expr ≫ »(pi.π (λ
       p : «expr × »(ι, ι), F.obj (op «expr ⊓ »(U p.1, U p.2))) (j, index_of_hom U (hom_of_index U j)), F.map i_eq.op))) s.condition],
  dsimp [] [] [] ["at", ident this],
  rw ["[", expr category.assoc, ",", expr category.assoc, "]"] ["at", ident this],
  symmetry,
  convert [] [expr this] ["using", 2],
  { dunfold [ident left_res] [],
    rw ["[", expr limit.lift_π_assoc, ",", expr fan.mk_π_app, ",", expr category.assoc, ",", "<-", expr F.map_comp, "]"] [],
    erw [expr F.map_id] [],
    rw [expr category.comp_id] [] },
  { dunfold [ident right_res] [],
    rw ["[", expr limit.lift_π_assoc, ",", expr fan.mk_π_app, ",", expr category.assoc, ",", "<-", expr F.map_comp, "]"] [],
    congr }
end

/--
The canonical morphism from the second object of the spaces diagram to the second object of the
sites diagram.
-/
def pi_inters_to_second_obj : pi_inters F U ⟶ presheaf.second_obj.{v, v, u} (presieve_of_covering U) F :=
  pi.lift
    fun f =>
      pi.π _ (index_of_hom U f.fst, index_of_hom U f.snd) ≫
        F.map
          (eq_to_hom
              (by 
                rw [complete_lattice.pullback_eq_inf, ←index_of_hom_spec U, ←index_of_hom_spec U])).op

theorem pi_opens_to_first_obj_comp_fist_map_eq :
  pi_opens_to_first_obj F U ≫ presheaf.first_map (presieve_of_covering U) F =
    left_res F U ≫ pi_inters_to_second_obj F U :=
  by 
    ext ⟨f, g⟩
    dunfold pi_opens_to_first_obj presheaf.first_map left_res pi_inters_to_second_obj 
    rw [category.assoc, category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, ←category.assoc,
      ←category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, category.assoc, category.assoc,
      ←F.map_comp, ←F.map_comp]
    rfl

theorem pi_opens_to_first_obj_comp_second_map_eq :
  pi_opens_to_first_obj F U ≫ presheaf.second_map (presieve_of_covering U) F =
    right_res F U ≫ pi_inters_to_second_obj F U :=
  by 
    ext ⟨f, g⟩
    dunfold pi_opens_to_first_obj presheaf.second_map right_res pi_inters_to_second_obj 
    rw [category.assoc, category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, ←category.assoc,
      ←category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, category.assoc, category.assoc,
      ←F.map_comp, ←F.map_comp]
    rfl

theorem fork_map_comp_first_map_to_pi_opens_eq :
  presheaf.fork_map (presieve_of_covering U) F ≫ first_obj_to_pi_opens F U = res F U :=
  by 
    ext i 
    dsimp [presheaf.fork_map, first_obj_to_pi_opens, res]
    rw [category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app]
    rfl

theorem res_comp_pi_opens_to_first_obj_eq :
  res F U ≫ pi_opens_to_first_obj F U = presheaf.fork_map (presieve_of_covering U) F :=
  by 
    ext f 
    dunfold res pi_opens_to_first_obj presheaf.fork_map 
    rw [category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, ←category.assoc, limit.lift_π,
      fan.mk_π_app, ←F.map_comp]
    congr

end PresieveOfCovering

open PresieveOfCovering

theorem is_sheaf_spaces_of_is_sheaf_sites (Fsh : presheaf.is_sheaf (Opens.grothendieckTopology X) F) : F.is_sheaf :=
  by 
    intro ι U 
    rw [presheaf.is_sheaf_iff_is_sheaf'] at Fsh 
    obtain ⟨h_limit⟩ := Fsh (supr U) (presieve_of_covering U) (presieve_of_covering.mem_grothendieck_topology U)
    refine' ⟨fork.is_limit.mk' _ _⟩
    intro s 
    obtain ⟨l, hl⟩ := fork.is_limit.lift' h_limit (s.ι ≫ pi_opens_to_first_obj F U) _ 
    swap
    ·
      rw [category.assoc, category.assoc, pi_opens_to_first_obj_comp_fist_map_eq,
        pi_opens_to_first_obj_comp_second_map_eq, ←category.assoc, ←category.assoc, s.condition]
    refine' ⟨l, _, _⟩
    ·
      rw [←fork_ι_comp_pi_opens_to_first_obj_to_pi_opens_eq F U s, ←category.assoc, ←hl, category.assoc, fork.ι_of_ι,
        fork_map_comp_first_map_to_pi_opens_eq]
      rfl
    ·
      intro m hm 
      apply fork.is_limit.hom_ext h_limit 
      rw [hl, fork.ι_of_ι]
      simpRw [←res_comp_pi_opens_to_first_obj_eq]
      erw [←category.assoc, hm]

theorem is_sheaf_sites_iff_is_sheaf_spaces : presheaf.is_sheaf (Opens.grothendieckTopology X) F ↔ F.is_sheaf :=
  Iff.intro (is_sheaf_spaces_of_is_sheaf_sites F) (is_sheaf_sites_of_is_sheaf_spaces F)

variable(C X)

/-- Turn a sheaf on the site `opens X` into a sheaf on the space `X`. -/
@[simps]
def Sheaf_sites_to_sheaf_spaces : Sheaf (Opens.grothendieckTopology X) C ⥤ sheaf C X :=
  { obj := fun F => ⟨F.1, is_sheaf_spaces_of_is_sheaf_sites F.1 F.2⟩, map := fun F G f => f }

/-- Turn a sheaf on the space `X` into a sheaf on the site `opens X`. -/
@[simps]
def Sheaf_spaces_to_sheaf_sites : sheaf C X ⥤ Sheaf (Opens.grothendieckTopology X) C :=
  { obj := fun F => ⟨F.1, is_sheaf_sites_of_is_sheaf_spaces F.1 F.2⟩, map := fun F G f => f }

/--
The equivalence of categories between sheaves on the site `opens X` and sheaves on the space `X`.
-/
@[simps]
def Sheaf_spaces_equivelence_sheaf_sites : Sheaf (Opens.grothendieckTopology X) C ≌ sheaf C X :=
  by 
    refine' equivalence.mk (Sheaf_sites_to_sheaf_spaces C X) (Sheaf_spaces_to_sheaf_sites C X) _ _ 
    all_goals 
      refine' nat_iso.of_components (fun F => eq_to_iso (Subtype.ext rfl)) fun F G f => _ 
      ext U 
      dsimp 
      erw [nat_trans.comp_app, nat_trans.comp_app, eq_to_hom_refl G.1 rfl, eq_to_hom_refl F.1 rfl, nat_trans.id_app G.1,
        category.comp_id, nat_trans.id_app F.1, category.id_comp]

end Top.Presheaf

namespace Top.Opens

open CategoryTheory TopologicalSpace

variable{X : Top}{ι : Type _}

theorem cover_dense_iff_is_basis [category ι] (B : ι ⥤ opens X) :
  cover_dense (Opens.grothendieckTopology X) B ↔ opens.is_basis (Set.Range B.obj) :=
  by 
    rw [opens.is_basis_iff_nbhd]
    split 
    intro hd U x hx 
    rcases hd.1 U x hx with ⟨V, f, ⟨i, f₁, f₂, hc⟩, hV⟩
    exact ⟨B.obj i, ⟨i, rfl⟩, f₁.le hV, f₂.le⟩
    intro hb 
    split 
    intro U x hx 
    rcases hb hx with ⟨_, ⟨i, rfl⟩, hx, hi⟩
    exact ⟨B.obj i, ⟨⟨hi⟩⟩, ⟨⟨i, 𝟙 _, ⟨⟨hi⟩⟩, rfl⟩⟩, hx⟩

theorem cover_dense_induced_functor {B : ι → opens X} (h : opens.is_basis (Set.Range B)) :
  cover_dense (Opens.grothendieckTopology X) (induced_functor B) :=
  (cover_dense_iff_is_basis _).2 h

end Top.Opens

namespace Top.Sheaf

open CategoryTheory TopologicalSpace Top Opposite

variable{C : Type u}[category.{v} C][limits.has_products C]

variable{X : Top.{v}}{ι : Type _}{B : ι → opens X}

variable(F : presheaf C X)(F' : sheaf C X)(h : opens.is_basis (Set.Range B))

/-- If a family `B` of open sets forms a basis of the topology on `X`, and if `F'`
    is a sheaf on `X`, then a homomorphism between a presheaf `F` on `X` and `F'`
    is equivalent to a homomorphism between their restrictions to the indexing type
    `ι` of `B`, with the induced category structure on `ι`. -/
def restrict_hom_equiv_hom : ((induced_functor B).op ⋙ F ⟶ (induced_functor B).op ⋙ F'.1) ≃ (F ⟶ F'.1) :=
  @cover_dense.restrict_hom_equiv_hom _ _ _ _ _ _ _ _ (opens.cover_dense_induced_functor h) _ F
    ((presheaf.Sheaf_spaces_to_sheaf_sites C X).obj F')

@[simp]
theorem extend_hom_app (α : (induced_functor B).op ⋙ F ⟶ (induced_functor B).op ⋙ F'.1) (i : ι) :
  (restrict_hom_equiv_hom F F' h α).app (op (B i)) = α.app (op i) :=
  by 
    nthRw 1[←(restrict_hom_equiv_hom F F' h).left_inv α]
    rfl

include h

theorem hom_ext {α β : F ⟶ F'.1} (he : ∀ i, α.app (op (B i)) = β.app (op (B i))) : α = β :=
  by 
    apply (restrict_hom_equiv_hom F F' h).symm.Injective 
    ext i 
    exact he i.unop

end Top.Sheaf

