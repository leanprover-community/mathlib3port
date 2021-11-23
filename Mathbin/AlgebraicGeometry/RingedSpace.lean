import Mathbin.Algebra.Category.CommRing.FilteredColimits 
import Mathbin.AlgebraicGeometry.SheafedSpace 
import Mathbin.Topology.Sheaves.Stalks 
import Mathbin.Algebra.Category.CommRing.Colimits 
import Mathbin.Algebra.Category.CommRing.Limits

/-!
# Ringed spaces

We introduce the category of ringed spaces, as an alias for `SheafedSpace CommRing`.

The facts collected in this file are typically stated for locally ringed spaces, but never actually
make use of the locality of stalks. See for instance https://stacks.math.columbia.edu/tag/01HZ.

-/


universe v

open CategoryTheory

open TopologicalSpace

open Opposite

open Top

open Top.Presheaf

namespace AlgebraicGeometry

/-- The type of Ringed spaces, as an abbreviation for `SheafedSpace CommRing`. -/
abbrev RingedSpace : Type _ :=
  SheafedSpace CommRingₓₓ

namespace RingedSpace

open SheafedSpace

variable(X : RingedSpace.{v})

-- error in AlgebraicGeometry.RingedSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If the germ of a section `f` is a unit in the stalk at `x`, then `f` must be a unit on some small
neighborhood around `x`.
-/
theorem is_unit_res_of_is_unit_germ
(U : opens X)
(f : X.presheaf.obj (op U))
(x : U)
(h : is_unit (X.presheaf.germ x f)) : «expr∃ , »((V : opens X)
 (i : «expr ⟶ »(V, U))
 (hxV : «expr ∈ »(x.1, V)), is_unit (X.presheaf.map i.op f)) :=
begin
  obtain ["⟨", ident g', ",", ident heq, "⟩", ":=", expr h.exists_right_inv],
  obtain ["⟨", ident V, ",", ident hxV, ",", ident g, ",", ident rfl, "⟩", ":=", expr X.presheaf.germ_exist x.1 g'],
  let [ident W] [] [":=", expr «expr ⊓ »(U, V)],
  have [ident hxW] [":", expr «expr ∈ »(x.1, W)] [":=", expr ⟨x.2, hxV⟩],
  erw ["[", "<-", expr X.presheaf.germ_res_apply (opens.inf_le_left U V) ⟨x.1, hxW⟩ f, ",", "<-", expr X.presheaf.germ_res_apply (opens.inf_le_right U V) ⟨x.1, hxW⟩ g, ",", "<-", expr ring_hom.map_mul, ",", "<-", expr ring_hom.map_one (X.presheaf.germ (⟨x.1, hxW⟩ : W)), "]"] ["at", ident heq],
  obtain ["⟨", ident W', ",", ident hxW', ",", ident i₁, ",", ident i₂, ",", ident heq', "⟩", ":=", expr X.presheaf.germ_eq x.1 hxW hxW _ _ heq],
  use ["[", expr W', ",", expr «expr ≫ »(i₁, opens.inf_le_left U V), ",", expr hxW', "]"],
  rw ["[", expr ring_hom.map_one, ",", expr ring_hom.map_mul, ",", "<-", expr comp_apply, ",", "<-", expr X.presheaf.map_comp, ",", "<-", expr op_comp, "]"] ["at", ident heq'],
  exact [expr is_unit_of_mul_eq_one _ _ heq']
end

-- error in AlgebraicGeometry.RingedSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a section `f` is a unit in each stalk, `f` must be a unit. -/
theorem is_unit_of_is_unit_germ
(U : opens X)
(f : X.presheaf.obj (op U))
(h : ∀ x : U, is_unit (X.presheaf.germ x f)) : is_unit f :=
begin
  choose [] [ident V] [ident iVU, ident m, ident h_unit] ["using", expr λ
   x : U, X.is_unit_res_of_is_unit_germ U f x (h x)],
  have [ident hcover] [":", expr «expr ≤ »(U, supr V)] [],
  { intros [ident x, ident hxU],
    rw ["[", expr opens.mem_coe, ",", expr opens.mem_supr, "]"] [],
    exact [expr ⟨⟨x, hxU⟩, m ⟨x, hxU⟩⟩] },
  choose [] [ident g] [ident hg] ["using", expr λ x : U, is_unit.exists_right_inv (h_unit x)],
  obtain ["⟨", ident gl, ",", ident gl_spec, ",", "-", "⟩", ":=", expr X.sheaf.exists_unique_gluing' V U iVU hcover g _],
  swap,
  { intros [ident x, ident y],
    apply [expr section_ext X.sheaf «expr ⊓ »(V x, V y)],
    rintro ["⟨", ident z, ",", ident hzVx, ",", ident hzVy, "⟩"],
    rw ["[", expr germ_res_apply, ",", expr germ_res_apply, "]"] [],
    apply [expr (is_unit.mul_right_inj (h ⟨z, (iVU x).le hzVx⟩)).mp],
    erw ["[", "<-", expr X.presheaf.germ_res_apply (iVU x) ⟨z, hzVx⟩ f, ",", "<-", expr ring_hom.map_mul, ",", expr congr_arg (X.presheaf.germ (⟨z, hzVx⟩ : V x)) (hg x), ",", expr germ_res_apply, ",", "<-", expr X.presheaf.germ_res_apply (iVU y) ⟨z, hzVy⟩ f, ",", "<-", expr ring_hom.map_mul, ",", expr congr_arg (X.presheaf.germ (⟨z, hzVy⟩ : V y)) (hg y), ",", expr ring_hom.map_one, ",", expr ring_hom.map_one, "]"] [] },
  apply [expr is_unit_of_mul_eq_one f gl],
  apply [expr X.sheaf.eq_of_locally_eq' V U iVU hcover],
  intro [ident i],
  rw ["[", expr ring_hom.map_one, ",", expr ring_hom.map_mul, ",", expr gl_spec, "]"] [],
  exact [expr hg i]
end

/--
The basic open of a global section `f` is the set of all points `x`, such that the germ of `f` at
`x` is a unit.
-/
def basic_open (f : Γ.obj (op X)) : opens X :=
  { val := { x:X | IsUnit (X.presheaf.germ (⟨x, trivialₓ⟩ : (⊤ : opens X)) f) },
    property :=
      by 
        rw [is_open_iff_forall_mem_open]
        intro x hx 
        obtain ⟨U, i, hxU, hf⟩ := X.is_unit_res_of_is_unit_germ ⊤ f ⟨x, trivialₓ⟩ hx 
        use U.1
        refine' ⟨_, U.2, hxU⟩
        intro y hy 
        rw [Set.mem_set_of_eq]
        convert RingHom.is_unit_map (X.presheaf.germ ⟨y, hy⟩) hf 
        exact (X.presheaf.germ_res_apply i ⟨y, hy⟩ f).symm }

@[simp]
theorem mem_basic_open (f : Γ.obj (op X)) (x : X) :
  x ∈ X.basic_open f ↔ IsUnit (X.presheaf.germ (⟨x, trivialₓ⟩ : (⊤ : opens X)) f) :=
  Iff.rfl

/-- The restriction of a global section `f` to the basic open of `f` is a unit. -/
theorem is_unit_res_basic_open (f : Γ.obj (op X)) : IsUnit (X.presheaf.map (opens.le_top (X.basic_open f)).op f) :=
  by 
    apply is_unit_of_is_unit_germ 
    rintro ⟨x, hx⟩
    convert hx 
    rw [germ_res_apply]
    rfl

end RingedSpace

end AlgebraicGeometry

