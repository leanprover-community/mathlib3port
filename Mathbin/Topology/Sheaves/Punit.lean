/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

! This file was ported from Lean 3 source module topology.sheaves.punit
! leanprover-community/mathlib commit ffc3730d545623aedf5d5bd46a3153cbf41f6c2c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Sheaves.SheafCondition.Sites

/-!
# Presheaves on punit

Presheaves on punit satisfy sheaf condition iff its value at empty set is a terminal object.
-/


namespace TopCat.Presheaf

universe u v w

open CategoryTheory CategoryTheory.Limits TopCat Opposite

variable {C : Type u} [Category.{v} C]

theorem is_sheaf_of_is_terminal_of_indiscrete {X : TopCat.{w}} (hind : X.str = ⊤) (F : Presheaf C X)
    (it : is_terminal <| F.obj <| op ⊥) : F.IsSheaf := fun c U s hs =>
  by
  obtain rfl | hne := eq_or_ne U ⊥
  · intro _ _
    rw [@exists_unique_iff_exists _ ⟨fun _ _ => _⟩]
    · refine' ⟨it.from _, fun U hU hs => is_terminal.hom_ext _ _ _⟩
      rwa [le_bot_iff.1 hU.le]
    · apply it.hom_ext
  · convert presieve.is_sheaf_for_top_sieve _
    rw [← sieve.id_mem_iff_eq_top]
    have := (U.eq_bot_or_top hind).resolve_left hne
    subst this
    obtain he | ⟨⟨x⟩⟩ := isEmpty_or_nonempty X
    · exact (hne <| TopologicalSpace.Opens.ext_iff.1 <| Set.univ_eq_empty_iff.2 he).elim
    obtain ⟨U, f, hf, hm⟩ := hs x trivial
    obtain rfl | rfl := U.eq_bot_or_top hind
    · cases hm
    · convert hf
#align
  Top.presheaf.is_sheaf_of_is_terminal_of_indiscrete TopCat.Presheaf.is_sheaf_of_is_terminal_of_indiscrete

theorem is_sheaf_iff_is_terminal_of_indiscrete {X : TopCat.{w}} (hind : X.str = ⊤)
    (F : Presheaf C X) : F.IsSheaf ↔ Nonempty (is_terminal <| F.obj <| op ⊥) :=
  ⟨fun h => ⟨Sheaf.isTerminalOfEmpty ⟨F, h⟩⟩, fun ⟨it⟩ =>
    is_sheaf_of_is_terminal_of_indiscrete hind F it⟩
#align
  Top.presheaf.is_sheaf_iff_is_terminal_of_indiscrete TopCat.Presheaf.is_sheaf_iff_is_terminal_of_indiscrete

theorem is_sheaf_on_punit_of_is_terminal (F : Presheaf C (TopCat.of PUnit))
    (it : is_terminal <| F.obj <| op ⊥) : F.IsSheaf :=
  is_sheaf_of_is_terminal_of_indiscrete (@Subsingleton.elim (TopologicalSpace PUnit) _ _ _) F it
#align
  Top.presheaf.is_sheaf_on_punit_of_is_terminal TopCat.Presheaf.is_sheaf_on_punit_of_is_terminal

theorem is_sheaf_on_punit_iff_is_terminal (F : Presheaf C (TopCat.of PUnit)) :
    F.IsSheaf ↔ Nonempty (is_terminal <| F.obj <| op ⊥) :=
  ⟨fun h => ⟨Sheaf.isTerminalOfEmpty ⟨F, h⟩⟩, fun ⟨it⟩ => is_sheaf_on_punit_of_is_terminal F it⟩
#align
  Top.presheaf.is_sheaf_on_punit_iff_is_terminal TopCat.Presheaf.is_sheaf_on_punit_iff_is_terminal

end TopCat.Presheaf

