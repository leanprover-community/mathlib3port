import Mathbin.Algebra.Category.Module.EpiMono 
import Mathbin.CategoryTheory.Subobject.WellPowered

/-!
# Subobjects in the category of `R`-modules

We construct an explicit order isomorphism between the categorical subobjects of an `R`-module `M`
and its submodules. This immediately implies that the category of `R`-modules is well-powered.

-/


open CategoryTheory

open CategoryTheory.Subobject

open_locale ModuleCat

universe v u

namespace ModuleCat

variable{R : Type u}[Ringₓ R](M : ModuleCat.{v} R)

-- error in Algebra.Category.Module.Subobject: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The categorical subobjects of a module `M` are in one-to-one correspondence with its
    submodules.-/ noncomputable def subobject_Module : «expr ≃o »(subobject M, submodule R M) :=
order_iso.symm { inv_fun := λ S, S.arrow.range,
  to_fun := λ N, subobject.mk «expr↾ »(N.subtype),
  right_inv := λ
  S, eq.symm (begin
     fapply [expr eq_mk_of_comm],
     { apply [expr linear_equiv.to_Module_iso'_left],
       apply [expr linear_equiv.of_bijective (linear_map.cod_restrict S.arrow.range S.arrow _)],
       { simpa [] [] ["only"] ["[", "<-", expr linear_map.ker_eq_bot, ",", expr linear_map.ker_cod_restrict, "]"] [] ["using", expr ker_eq_bot_of_mono _] },
       { rw ["[", "<-", expr linear_map.range_eq_top, ",", expr linear_map.range_cod_restrict, ",", expr submodule.comap_subtype_self, "]"] [] },
       { exact [expr linear_map.mem_range_self _] } },
     { apply [expr linear_map.ext],
       intros [ident x],
       refl }
   end),
  left_inv := λ N, begin
    convert [] [expr congr_arg linear_map.range (underlying_iso_arrow «expr↾ »(N.subtype))] ["using", 1],
    { have [] [":", expr «expr = »((underlying_iso «expr↾ »(N.subtype)).inv, (underlying_iso «expr↾ »(N.subtype)).symm.to_linear_equiv)] [],
      { apply [expr linear_map.ext],
        intros [ident x],
        refl },
      rw ["[", expr this, ",", expr comp_def, ",", expr linear_equiv.range_comp, "]"] [] },
    { exact [expr (submodule.range_subtype _).symm] }
  end,
  map_rel_iff' := λ S T, begin
    refine [expr ⟨λ h, _, λ h, mk_le_mk_of_comm «expr↟ »(submodule.of_le h) (by { ext [] [] [], refl })⟩],
    convert [] [expr linear_map.range_comp_le_range (of_mk_le_mk _ _ h) «expr↾ »(T.subtype)] [],
    { simpa [] [] ["only"] ["[", "<-", expr comp_def, ",", expr of_mk_le_mk_comp, "]"] [] ["using", expr (submodule.range_subtype _).symm] },
    { exact [expr (submodule.range_subtype _).symm] }
  end }

instance well_powered_Module : well_powered (ModuleCat.{v} R) :=
  ⟨fun M => ⟨⟨_, ⟨(subobject_Module M).toEquiv⟩⟩⟩⟩

end ModuleCat

