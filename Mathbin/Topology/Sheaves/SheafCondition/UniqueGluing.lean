import Mathbin.Topology.Sheaves.Forget 
import Mathbin.CategoryTheory.Limits.Shapes.Types 
import Mathbin.Topology.Sheaves.Sheaf 
import Mathbin.CategoryTheory.Types

/-!
# The sheaf condition in terms of unique gluings

We provide an alternative formulation of the sheaf condition in terms of unique gluings.

We work with sheaves valued in a concrete category `C` admitting all limits, whose forgetful
functor `C ⥤ Type` preserves limits and reflects isomorphisms. The usual categories of algebraic
structures, such as `Mon`, `AddCommGroup`, `Ring`, `CommRing` etc. are all examples of this kind of
category.

A presheaf `F : presheaf C X` satisfies the sheaf condition if and only if, for every
compatible family of sections `sf : Π i : ι, F.obj (op (U i))`, there exists a unique gluing
`s : F.obj (op (supr U))`.

Here, the family `sf` is called compatible, if for all `i j : ι`, the restrictions of `sf i`
and `sf j` to `U i ⊓ U j` agree. A section `s : F.obj (op (supr U))` is a gluing for the
family `sf`, if `s` restricts to `sf i` on `U i` for all `i : ι`

We show that the sheaf condition in terms of unique gluings is equivalent to the definition
in terms of equalizers. Our approach is as follows: First, we show them to be equivalent for
`Type`-valued presheaves. Then we use that composing a presheaf with a limit-preserving and
isomorphism-reflecting functor leaves the sheaf condition invariant, as shown in
`topology/sheaves/forget.lean`.

-/


noncomputable theory

open Top

open Top.Presheaf

open Top.Presheaf.SheafConditionEqualizerProducts

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

open TopologicalSpace.Opens

open Opposite

universe u v

variable{C : Type u}[category.{v} C][concrete_category.{v} C]

namespace Top

namespace Presheaf

section 

attribute [local instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

variable{X : Top.{v}}(F : presheaf C X){ι : Type v}(U : ι → opens X)

/--
A family of sections `sf` is compatible, if the restrictions of `sf i` and `sf j` to `U i ⊓ U j`
agree, for all `i` and `j`
-/
def is_compatible (sf : ∀ i : ι, F.obj (op (U i))) : Prop :=
  ∀ i j : ι, F.map (inf_le_left (U i) (U j)).op (sf i) = F.map (inf_le_right (U i) (U j)).op (sf j)

/--
A section `s` is a gluing for a family of sections `sf` if it restricts to `sf i` on `U i`,
for all `i`
-/
def is_gluing (sf : ∀ i : ι, F.obj (op (U i))) (s : F.obj (op (supr U))) : Prop :=
  ∀ i : ι, F.map (opens.le_supr U i).op s = sf i

/--
The sheaf condition in terms of unique gluings. A presheaf `F : presheaf C X` satisfies this sheaf
condition if and only if, for every compatible family of sections `sf : Π i : ι, F.obj (op (U i))`,
there exists a unique gluing `s : F.obj (op (supr U))`.

We prove this to be equivalent to the usual one below in
`is_sheaf_iff_is_sheaf_unique_gluing`
-/
def is_sheaf_unique_gluing : Prop :=
  ∀ ⦃ι : Type v⦄ U : ι → opens X sf : ∀ i : ι, F.obj (op (U i)),
    is_compatible F U sf → ∃!s : F.obj (op (supr U)), is_gluing F U sf s

end 

section TypeValued

variable{X : Top.{v}}(F : presheaf (Type v) X){ι : Type v}(U : ι → opens X)

/--
For presheaves of types, terms of `pi_opens F U` are just families of sections.
-/
def pi_opens_iso_sections_family : pi_opens F U ≅ ∀ i : ι, F.obj (op (U i)) :=
  limits.is_limit.cone_point_unique_up_to_iso (limit.is_limit (discrete.functor fun i : ι => F.obj (op (U i))))
    (types.product_limit_cone fun i : ι => F.obj (op (U i))).IsLimit

/--
Under the isomorphism `pi_opens_iso_sections_family`, compatibility of sections is the same
as being equalized by the arrows `left_res` and `right_res` of the equalizer diagram.
-/
theorem compatible_iff_left_res_eq_right_res (sf : pi_opens F U) :
  is_compatible F U ((pi_opens_iso_sections_family F U).Hom sf) ↔ left_res F U sf = right_res F U sf :=
  by 
    split  <;> intro h
    ·
      ext ⟨i, j⟩
      rw [left_res, types.limit.lift_π_apply, fan.mk_π_app, right_res, types.limit.lift_π_apply, fan.mk_π_app]
      exact h i j
    ·
      intro i j 
      convert congr_argₓ (limits.pi.π (fun p : ι × ι => F.obj (op (U p.1⊓U p.2))) (i, j)) h
      ·
        rw [left_res, types.pi_lift_π_apply]
        rfl
      ·
        rw [right_res, types.pi_lift_π_apply]
        rfl

/--
Under the isomorphism `pi_opens_iso_sections_family`, being a gluing of a family of
sections `sf` is the same as lying in the preimage of `res` (the leftmost arrow of the
equalizer diagram).
-/
@[simp]
theorem is_gluing_iff_eq_res (sf : pi_opens F U) (s : F.obj (op (supr U))) :
  is_gluing F U ((pi_opens_iso_sections_family F U).Hom sf) s ↔ res F U s = sf :=
  by 
    split  <;> intro h
    ·
      ext i 
      rw [res, types.limit.lift_π_apply, fan.mk_π_app]
      exact h i
    ·
      intro i 
      convert congr_argₓ (limits.pi.π (fun i : ι => F.obj (op (U i))) i) h 
      rw [res, types.pi_lift_π_apply]
      rfl

-- error in Topology.Sheaves.SheafCondition.UniqueGluing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The "equalizer" sheaf condition can be obtained from the sheaf condition
in terms of unique gluings.
-/ theorem is_sheaf_of_is_sheaf_unique_gluing_types (Fsh : F.is_sheaf_unique_gluing) : F.is_sheaf :=
begin
  intros [ident ι, ident U],
  refine [expr ⟨fork.is_limit.mk' _ _⟩],
  intro [ident s],
  have [ident h_compatible] [":", expr ∀
   x : s.X, F.is_compatible U ((F.pi_opens_iso_sections_family U).hom (s.ι x))] [],
  { intro [ident x],
    rw [expr compatible_iff_left_res_eq_right_res] [],
    convert [] [expr congr_fun s.condition x] [] },
  choose [] [ident m] [ident m_spec, ident m_uniq] ["using", expr λ
   x : s.X, Fsh U ((pi_opens_iso_sections_family F U).hom (s.ι x)) (h_compatible x)],
  refine [expr ⟨m, _, _⟩],
  { ext [] [ident i, ident x] [],
    simp [] [] [] ["[", expr res, "]"] [] [],
    exact [expr m_spec x i] },
  { intros [ident l, ident hl],
    ext [] [ident x] [],
    apply [expr m_uniq],
    rw [expr is_gluing_iff_eq_res] [],
    exact [expr congr_fun hl x] }
end

-- error in Topology.Sheaves.SheafCondition.UniqueGluing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The sheaf condition in terms of unique gluings can be obtained from the usual
"equalizer" sheaf condition.
-/ theorem is_sheaf_unique_gluing_of_is_sheaf_types (Fsh : F.is_sheaf) : F.is_sheaf_unique_gluing :=
begin
  intros [ident ι, ident U, ident sf, ident hsf],
  let [ident sf'] [] [":=", expr (pi_opens_iso_sections_family F U).inv sf],
  have [ident hsf'] [":", expr «expr = »(left_res F U sf', right_res F U sf')] [],
  { rwa ["[", "<-", expr compatible_iff_left_res_eq_right_res F U sf', ",", expr inv_hom_id_apply, "]"] [] },
  choose [] [ident s] [ident s_spec, ident s_uniq] ["using", expr types.unique_of_type_equalizer _ _ (Fsh U).some sf' hsf'],
  use [expr s],
  dsimp [] [] [] [],
  split,
  { convert [] [expr (is_gluing_iff_eq_res F U sf' _).mpr s_spec] [],
    rw [expr inv_hom_id_apply] [] },
  { intros [ident y, ident hy],
    apply [expr s_uniq],
    rw ["<-", expr is_gluing_iff_eq_res F U] [],
    convert [] [expr hy] [],
    rw [expr inv_hom_id_apply] [] }
end

/--
For type-valued presheaves, the sheaf condition in terms of unique gluings is equivalent to the
usual sheaf condition in terms of equalizer diagrams.
-/
theorem is_sheaf_iff_is_sheaf_unique_gluing_types : F.is_sheaf ↔ F.is_sheaf_unique_gluing :=
  Iff.intro (is_sheaf_unique_gluing_of_is_sheaf_types F) (is_sheaf_of_is_sheaf_unique_gluing_types F)

end TypeValued

section 

attribute [local instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

variable[has_limits C][reflects_isomorphisms (forget C)][preserves_limits (forget C)]

variable{X : Top.{v}}(F : presheaf C X){ι : Type v}(U : ι → opens X)

/--
For presheaves valued in a concrete category, whose forgetful functor reflects isomorphisms and
preserves limits, the sheaf condition in terms of unique gluings is equivalent to the usual one
in terms of equalizer diagrams.
-/
theorem is_sheaf_iff_is_sheaf_unique_gluing : F.is_sheaf ↔ F.is_sheaf_unique_gluing :=
  Iff.trans (is_sheaf_iff_is_sheaf_comp (forget C) F) (is_sheaf_iff_is_sheaf_unique_gluing_types (F ⋙ forget C))

end 

end Presheaf

namespace Sheaf

open Presheaf

open CategoryTheory

section 

attribute [local instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

variable[has_limits C][reflects_isomorphisms (concrete_category.forget C)]

variable[preserves_limits (concrete_category.forget C)]

variable{X : Top.{v}}(F : sheaf C X){ι : Type v}(U : ι → opens X)

/--
A more convenient way of obtaining a unique gluing of sections for a sheaf.
-/
theorem exists_unique_gluing (sf : ∀ i : ι, F.1.obj (op (U i))) (h : is_compatible F.1 U sf) :
  ∃!s : F.1.obj (op (supr U)), is_gluing F.1 U sf s :=
  (is_sheaf_iff_is_sheaf_unique_gluing F.1).mp F.property U sf h

-- error in Topology.Sheaves.SheafCondition.UniqueGluing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
In this version of the lemma, the inclusion homs `iUV` can be specified directly by the user,
which can be more convenient in practice.
-/
theorem exists_unique_gluing'
(V : opens X)
(iUV : ∀ i : ι, «expr ⟶ »(U i, V))
(hcover : «expr ≤ »(V, supr U))
(sf : ∀ i : ι, F.1.obj (op (U i)))
(h : is_compatible F.1 U sf) : «expr∃! , »((s : F.1.obj (op V)), ∀ i : ι, «expr = »(F.1.map (iUV i).op s, sf i)) :=
begin
  have [ident V_eq_supr_U] [":", expr «expr = »(V, supr U)] [":=", expr le_antisymm hcover (supr_le (λ i, (iUV i).le))],
  obtain ["⟨", ident gl, ",", ident gl_spec, ",", ident gl_uniq, "⟩", ":=", expr F.exists_unique_gluing U sf h],
  refine [expr ⟨F.1.map (eq_to_hom V_eq_supr_U).op gl, _, _⟩],
  { intro [ident i],
    rw ["[", "<-", expr comp_apply, ",", "<-", expr F.1.map_comp, "]"] [],
    exact [expr gl_spec i] },
  { intros [ident gl', ident gl'_spec],
    convert [] [expr congr_arg _ (gl_uniq (F.1.map (eq_to_hom V_eq_supr_U.symm).op gl') (λ
       i, _))] []; rw ["[", "<-", expr comp_apply, ",", "<-", expr F.1.map_comp, "]"] [],
    { rw ["[", expr eq_to_hom_op, ",", expr eq_to_hom_op, ",", expr eq_to_hom_trans, ",", expr eq_to_hom_refl, ",", expr F.1.map_id, ",", expr id_apply, "]"] [] },
    { convert [] [expr gl'_spec i] [] } }
end

-- error in Topology.Sheaves.SheafCondition.UniqueGluing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[ext #[]]
theorem eq_of_locally_eq
(s t : F.1.obj (op (supr U)))
(h : ∀ i, «expr = »(F.1.map (opens.le_supr U i).op s, F.1.map (opens.le_supr U i).op t)) : «expr = »(s, t) :=
begin
  let [ident sf] [":", expr ∀ i : ι, F.1.obj (op (U i))] [":=", expr λ i, F.1.map (opens.le_supr U i).op s],
  have [ident sf_compatible] [":", expr is_compatible _ U sf] [],
  { intros [ident i, ident j],
    simp_rw ["[", "<-", expr comp_apply, ",", "<-", expr F.1.map_comp, "]"] [],
    refl },
  obtain ["⟨", ident gl, ",", "-", ",", ident gl_uniq, "⟩", ":=", expr F.exists_unique_gluing U sf sf_compatible],
  transitivity [expr gl],
  { apply [expr gl_uniq],
    intro [ident i],
    refl },
  { symmetry,
    apply [expr gl_uniq],
    intro [ident i],
    rw ["<-", expr h] [] }
end

-- error in Topology.Sheaves.SheafCondition.UniqueGluing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
In this version of the lemma, the inclusion homs `iUV` can be specified directly by the user,
which can be more convenient in practice.
-/
theorem eq_of_locally_eq'
(V : opens X)
(iUV : ∀ i : ι, «expr ⟶ »(U i, V))
(hcover : «expr ≤ »(V, supr U))
(s t : F.1.obj (op V))
(h : ∀ i, «expr = »(F.1.map (iUV i).op s, F.1.map (iUV i).op t)) : «expr = »(s, t) :=
begin
  have [ident V_eq_supr_U] [":", expr «expr = »(V, supr U)] [":=", expr le_antisymm hcover (supr_le (λ i, (iUV i).le))],
  suffices [] [":", expr «expr = »(F.1.map (eq_to_hom V_eq_supr_U.symm).op s, F.1.map (eq_to_hom V_eq_supr_U.symm).op t)],
  { convert [] [expr congr_arg (F.1.map (eq_to_hom V_eq_supr_U).op) this] []; rw ["[", "<-", expr comp_apply, ",", "<-", expr F.1.map_comp, ",", expr eq_to_hom_op, ",", expr eq_to_hom_op, ",", expr eq_to_hom_trans, ",", expr eq_to_hom_refl, ",", expr F.1.map_id, ",", expr id_apply, "]"] [] },
  apply [expr eq_of_locally_eq],
  intro [ident i],
  rw ["[", "<-", expr comp_apply, ",", "<-", expr comp_apply, ",", "<-", expr F.1.map_comp, "]"] [],
  convert [] [expr h i] []
end

end 

end Sheaf

end Top

