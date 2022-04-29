/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathbin.Algebra.Hom.GroupInstances
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Topology.UniformSpace.Completion

/-!
# Completion of topological groups:

This files endows the completion of a topological abelian group with a group structure.
More precisely the instance `uniform_space.completion.add_group` builds an abelian group structure
on the completion of an abelian group endowed with a compatible uniform structure.
Then the instance `uniform_space.completion.uniform_add_group` proves this group structure is
compatible with the completed uniform structure. The compatibility condition is `uniform_add_group`.

## Main declarations:

Beyond the instances explained above (that don't have to be explicitly invoked),
the main constructions deal with continuous group morphisms.

* `add_monoid_hom.extension`: extends a continuous group morphism from `G`
  to a complete separated group `H` to `completion G`.
* `add_monoid_hom.completion`: promotes a continuous group morphism
  from `G` to `H` into a continuous group morphism
  from `completion G` to `completion H`.
-/


noncomputable section

universe u v

section Groupₓ

open UniformSpace Cauchyₓ Filter Set

variable {α : Type u} [UniformSpace α]

instance [Zero α] : Zero (Completion α) :=
  ⟨(0 : α)⟩

instance [Neg α] : Neg (Completion α) :=
  ⟨Completion.map (fun a => -a : α → α)⟩

instance [Add α] : Add (Completion α) :=
  ⟨Completion.map₂ (· + ·)⟩

instance [Sub α] : Sub (Completion α) :=
  ⟨Completion.map₂ Sub.sub⟩

@[norm_cast]
theorem UniformSpace.Completion.coe_zero [Zero α] : ((0 : α) : Completion α) = 0 :=
  rfl

end Groupₓ

namespace UniformSpace.Completion

section UniformAddGroup

open UniformSpace UniformSpace.Completion

variable {α : Type _} [UniformSpace α] [AddGroupₓ α] [UniformAddGroup α]

@[norm_cast]
theorem coe_neg (a : α) : ((-a : α) : Completion α) = -a :=
  (map_coe uniform_continuous_neg a).symm

@[norm_cast]
theorem coe_sub (a b : α) : ((a - b : α) : Completion α) = a - b :=
  (map₂_coe_coe a b Sub.sub uniform_continuous_sub).symm

@[norm_cast]
theorem coe_add (a b : α) : ((a + b : α) : Completion α) = a + b :=
  (map₂_coe_coe a b (· + ·) uniform_continuous_add).symm

instance : AddMonoidₓ (Completion α) :=
  { Completion.hasZero, Completion.hasNeg, Completion.hasAdd, Completion.hasSub with
    zero_add := fun a =>
      Completion.induction_on a (is_closed_eq (continuous_map₂ continuous_const continuous_id) continuous_id) fun a =>
        show 0 + (a : Completion α) = a by
          rw_mod_cast[zero_addₓ],
    add_zero := fun a =>
      Completion.induction_on a (is_closed_eq (continuous_map₂ continuous_id continuous_const) continuous_id) fun a =>
        show (a : Completion α) + 0 = a by
          rw_mod_cast[add_zeroₓ],
    add_assoc := fun a b c =>
      Completion.induction_on₃ a b c
        (is_closed_eq
          (continuous_map₂ (continuous_map₂ continuous_fst (continuous_fst.comp continuous_snd))
            (continuous_snd.comp continuous_snd))
          (continuous_map₂ continuous_fst
            (continuous_map₂ (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))))
        fun a b c =>
        show (a : Completion α) + b + c = a + (b + c) by
          repeat'
            rw_mod_cast[add_assocₓ] }

instance : SubNegMonoidₓ (Completion α) :=
  { Completion.addMonoid, Completion.hasNeg, Completion.hasSub with
    sub_eq_add_neg := fun a b =>
      Completion.induction_on₂ a b
        (is_closed_eq (continuous_map₂ continuous_fst continuous_snd)
          (continuous_map₂ continuous_fst (Completion.continuous_map.comp continuous_snd)))
        fun a b => by
        exact_mod_cast congr_argₓ coe (sub_eq_add_neg a b) }

instance : AddGroupₓ (Completion α) :=
  { Completion.subNegMonoid with
    add_left_neg := fun a =>
      Completion.induction_on a
        (is_closed_eq (continuous_map₂ Completion.continuous_map continuous_id) continuous_const) fun a =>
        show -(a : Completion α) + a = 0 by
          rw_mod_cast[add_left_negₓ]
          rfl }

instance : UniformAddGroup (Completion α) :=
  ⟨uniform_continuous_map₂ Sub.sub⟩

/-- The map from a group to its completion as a group hom. -/
@[simps]
def toCompl : α →+ Completion α where
  toFun := coe
  map_add' := coe_add
  map_zero' := coe_zero

theorem continuous_to_compl : Continuous (toCompl : α → Completion α) :=
  continuous_coe α

variable {β : Type v} [UniformSpace β] [AddGroupₓ β] [UniformAddGroup β]

instance {α : Type u} [UniformSpace α] [AddCommGroupₓ α] [UniformAddGroup α] : AddCommGroupₓ (Completion α) :=
  { Completion.addGroup with
    add_comm := fun a b =>
      Completion.induction_on₂ a b
        (is_closed_eq (continuous_map₂ continuous_fst continuous_snd) (continuous_map₂ continuous_snd continuous_fst))
        fun x y => by
        change ↑x + ↑y = ↑y + ↑x
        rw [← coe_add, ← coe_add, add_commₓ] }

end UniformAddGroup

end UniformSpace.Completion

section AddMonoidHom

variable {α β : Type _} [UniformSpace α] [AddGroupₓ α] [UniformAddGroup α] [UniformSpace β] [AddGroupₓ β]
  [UniformAddGroup β]

open UniformSpace UniformSpace.Completion

/-- Extension to the completion of a continuous group hom. -/
def AddMonoidHom.extension [CompleteSpace β] [SeparatedSpace β] (f : α →+ β) (hf : Continuous f) : Completion α →+ β :=
  have hf : UniformContinuous f := uniform_continuous_add_monoid_hom_of_continuous hf
  { toFun := Completion.extension f,
    map_zero' := by
      rw [← coe_zero, extension_coe hf, f.map_zero],
    map_add' := fun a b =>
      Completion.induction_on₂ a b
        (is_closed_eq (continuous_extension.comp continuous_add)
          ((continuous_extension.comp continuous_fst).add (continuous_extension.comp continuous_snd)))
        fun a b => by
        rw_mod_cast[extension_coe hf, extension_coe hf, extension_coe hf, f.map_add] }

theorem AddMonoidHom.extension_coe [CompleteSpace β] [SeparatedSpace β] (f : α →+ β) (hf : Continuous f) (a : α) :
    f.extension hf a = f a :=
  extension_coe (uniform_continuous_add_monoid_hom_of_continuous hf) a

@[continuity]
theorem AddMonoidHom.continuous_extension [CompleteSpace β] [SeparatedSpace β] (f : α →+ β) (hf : Continuous f) :
    Continuous (f.extension hf) :=
  continuous_extension

/-- Completion of a continuous group hom, as a group hom. -/
def AddMonoidHom.completion (f : α →+ β) (hf : Continuous f) : Completion α →+ Completion β :=
  (toCompl.comp f).extension (continuous_to_compl.comp hf)

@[continuity]
theorem AddMonoidHom.continuous_completion (f : α →+ β) (hf : Continuous f) :
    Continuous (f.Completion hf : Completion α → Completion β) :=
  ContinuousMap

theorem AddMonoidHom.completion_coe (f : α →+ β) (hf : Continuous f) (a : α) : f.Completion hf a = f a :=
  map_coe (uniform_continuous_add_monoid_hom_of_continuous hf) a

theorem AddMonoidHom.completion_zero : (0 : α →+ β).Completion continuous_const = 0 := by
  ext x
  apply completion.induction_on x
  · apply is_closed_eq ((0 : α →+ β).continuous_completion continuous_const)
    simp [continuous_const]
    
  · intro a
    simp [(0 : α →+ β).completion_coe continuous_const, coe_zero]
    

theorem AddMonoidHom.completion_add {γ : Type _} [AddCommGroupₓ γ] [UniformSpace γ] [UniformAddGroup γ] (f g : α →+ γ)
    (hf : Continuous f) (hg : Continuous g) : (f + g).Completion (hf.add hg) = f.Completion hf + g.Completion hg := by
  have hfg := hf.add hg
  ext x
  apply completion.induction_on x
  · exact
      is_closed_eq ((f + g).continuous_completion hfg) ((f.continuous_completion hf).add (g.continuous_completion hg))
    
  · intro a
    simp [(f + g).completion_coe hfg, coe_add, f.completion_coe hf, g.completion_coe hg]
    

end AddMonoidHom

