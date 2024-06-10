/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Topology.UniformSpace.UniformEmbedding
import Topology.UniformSpace.Equiv

#align_import topology.uniform_space.abstract_completion from "leanprover-community/mathlib"@"34ee86e6a59d911a8e4f89b68793ee7577ae79c7"

/-!
# Abstract theory of Hausdorff completions of uniform spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file characterizes Hausdorff completions of a uniform space α as complete Hausdorff spaces
equipped with a map from α which has dense image and induce the original uniform structure on α.
Assuming these properties we "extend" uniformly continuous maps from α to complete Hausdorff spaces
to the completions of α. This is the universal property expected from a completion.
It is then used to extend uniformly continuous maps from α to α' to maps between
completions of α and α'.

This file does not construct any such completion, it only study consequences of their existence.
The first advantage is that formal properties are clearly highlighted without interference from
construction details. The second advantage is that this framework can then be used to compare
different completion constructions. See `topology/uniform_space/compare_reals` for an example.
Of course the comparison comes from the universal property as usual.

A general explicit construction of completions is done in `uniform_space/completion`, leading
to a functor from uniform spaces to complete Hausdorff uniform spaces that is left adjoint to the
inclusion, see `uniform_space/UniformSpace` for the category packaging.

## Implementation notes

A tiny technical advantage of using a characteristic predicate such as the properties listed in
`abstract_completion` instead of stating the universal property is that the universal property
derived from the predicate is more universe polymorphic.

## References

We don't know any traditional text discussing this. Real world mathematics simply silently
identify the results of any two constructions that lead to something one could reasonably
call a completion.

## Tags

uniform spaces, completion, universal property
-/


noncomputable section

attribute [local instance 10] Classical.propDecidable

open Filter Set Function

universe u

#print AbstractCompletion /-
/-- A completion of `α` is the data of a complete separated uniform space (from the same universe)
and a map from `α` with dense range and inducing the original uniform structure on `α`. -/
structure AbstractCompletion (α : Type u) [UniformSpace α] where
  Space : Type u
  coe : α → space
  uniformStruct : UniformSpace space
  complete : CompleteSpace space
  separation : T0Space space
  UniformInducing : UniformInducing coe
  dense : DenseRange coe
#align abstract_completion AbstractCompletion
-/

attribute [local instance] AbstractCompletion.uniformStruct AbstractCompletion.complete
  AbstractCompletion.separation

namespace AbstractCompletion

variable {α : Type _} [UniformSpace α] (pkg : AbstractCompletion α)

local notation "hatα" => pkg.Space

local notation "ι" => pkg.coe

#print AbstractCompletion.ofComplete /-
/-- If `α` is complete, then it is an abstract completion of itself. -/
def ofComplete [T0Space α] [CompleteSpace α] : AbstractCompletion α :=
  mk α id inferInstance inferInstance inferInstance uniformInducing_id denseRange_id
#align abstract_completion.of_complete AbstractCompletion.ofComplete
-/

#print AbstractCompletion.closure_range /-
theorem closure_range : closure (range ι) = univ :=
  pkg.dense.closure_range
#align abstract_completion.closure_range AbstractCompletion.closure_range
-/

#print AbstractCompletion.denseInducing /-
theorem denseInducing : DenseInducing ι :=
  ⟨pkg.UniformInducing.Inducing, pkg.dense⟩
#align abstract_completion.dense_inducing AbstractCompletion.denseInducing
-/

#print AbstractCompletion.uniformContinuous_coe /-
theorem uniformContinuous_coe : UniformContinuous ι :=
  UniformInducing.uniformContinuous pkg.UniformInducing
#align abstract_completion.uniform_continuous_coe AbstractCompletion.uniformContinuous_coe
-/

#print AbstractCompletion.continuous_coe /-
theorem continuous_coe : Continuous ι :=
  pkg.uniformContinuous_coe.Continuous
#align abstract_completion.continuous_coe AbstractCompletion.continuous_coe
-/

#print AbstractCompletion.induction_on /-
@[elab_as_elim]
theorem induction_on {p : hatα → Prop} (a : hatα) (hp : IsClosed {a | p a}) (ih : ∀ a, p (ι a)) :
    p a :=
  isClosed_property pkg.dense hp ih a
#align abstract_completion.induction_on AbstractCompletion.induction_on
-/

variable {β : Type _}

#print AbstractCompletion.funext /-
protected theorem funext [TopologicalSpace β] [T2Space β] {f g : hatα → β} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ a, f (ι a) = g (ι a)) : f = g :=
  funext fun a => pkg.inductionOn a (isClosed_eq hf hg) h
#align abstract_completion.funext AbstractCompletion.funext
-/

variable [UniformSpace β]

section Extend

#print AbstractCompletion.extend /-
/-- Extension of maps to completions -/
protected def extend (f : α → β) : hatα → β :=
  if UniformContinuous f then pkg.DenseInducing.extend f else fun x => f (pkg.dense.some x)
#align abstract_completion.extend AbstractCompletion.extend
-/

variable {f : α → β}

#print AbstractCompletion.extend_def /-
theorem extend_def (hf : UniformContinuous f) : pkg.extend f = pkg.DenseInducing.extend f :=
  if_pos hf
#align abstract_completion.extend_def AbstractCompletion.extend_def
-/

#print AbstractCompletion.extend_coe /-
theorem extend_coe [T2Space β] (hf : UniformContinuous f) (a : α) : (pkg.extend f) (ι a) = f a :=
  by
  rw [pkg.extend_def hf]
  exact pkg.dense_inducing.extend_eq hf.continuous a
#align abstract_completion.extend_coe AbstractCompletion.extend_coe
-/

variable [CompleteSpace β]

#print AbstractCompletion.uniformContinuous_extend /-
theorem uniformContinuous_extend : UniformContinuous (pkg.extend f) :=
  by
  by_cases hf : UniformContinuous f
  · rw [pkg.extend_def hf]
    exact uniformContinuous_uniformly_extend pkg.uniform_inducing pkg.dense hf
  · change UniformContinuous (ite _ _ _)
    rw [if_neg hf]
    exact uniformContinuous_of_const fun a b => by congr
#align abstract_completion.uniform_continuous_extend AbstractCompletion.uniformContinuous_extend
-/

#print AbstractCompletion.continuous_extend /-
theorem continuous_extend : Continuous (pkg.extend f) :=
  pkg.uniformContinuous_extend.Continuous
#align abstract_completion.continuous_extend AbstractCompletion.continuous_extend
-/

variable [T0Space β]

#print AbstractCompletion.extend_unique /-
theorem extend_unique (hf : UniformContinuous f) {g : hatα → β} (hg : UniformContinuous g)
    (h : ∀ a : α, f a = g (ι a)) : pkg.extend f = g :=
  by
  apply pkg.funext pkg.continuous_extend hg.continuous
  simpa only [pkg.extend_coe hf] using h
#align abstract_completion.extend_unique AbstractCompletion.extend_unique
-/

#print AbstractCompletion.extend_comp_coe /-
@[simp]
theorem extend_comp_coe {f : hatα → β} (hf : UniformContinuous f) : pkg.extend (f ∘ ι) = f :=
  funext fun x =>
    pkg.inductionOn x (isClosed_eq pkg.continuous_extend hf.Continuous) fun y =>
      pkg.extend_coe (hf.comp <| pkg.uniformContinuous_coe) y
#align abstract_completion.extend_comp_coe AbstractCompletion.extend_comp_coe
-/

end Extend

section MapSec

variable (pkg' : AbstractCompletion β)

local notation "hatβ" => pkg'.Space

local notation "ι'" => pkg'.coe

#print AbstractCompletion.map /-
/-- Lifting maps to completions -/
protected def map (f : α → β) : hatα → hatβ :=
  pkg.extend (ι' ∘ f)
#align abstract_completion.map AbstractCompletion.map
-/

local notation "map" => pkg.map pkg'

variable (f : α → β)

#print AbstractCompletion.uniformContinuous_map /-
theorem uniformContinuous_map : UniformContinuous (map f) :=
  pkg.uniformContinuous_extend
#align abstract_completion.uniform_continuous_map AbstractCompletion.uniformContinuous_map
-/

#print AbstractCompletion.continuous_map /-
theorem continuous_map : Continuous (map f) :=
  pkg.continuous_extend
#align abstract_completion.continuous_map AbstractCompletion.continuous_map
-/

variable {f}

#print AbstractCompletion.map_coe /-
@[simp]
theorem map_coe (hf : UniformContinuous f) (a : α) : map f (ι a) = ι' (f a) :=
  pkg.extend_coe (pkg'.uniformContinuous_coe.comp hf) a
#align abstract_completion.map_coe AbstractCompletion.map_coe
-/

#print AbstractCompletion.map_unique /-
theorem map_unique {f : α → β} {g : hatα → hatβ} (hg : UniformContinuous g)
    (h : ∀ a, ι' (f a) = g (ι a)) : map f = g :=
  pkg.funext (pkg.continuous_map _ _) hg.Continuous <|
    by
    intro a
    change pkg.extend (ι' ∘ f) _ = _
    simp only [(· ∘ ·), h]
    rw [pkg.extend_coe (hg.comp pkg.uniform_continuous_coe)]
#align abstract_completion.map_unique AbstractCompletion.map_unique
-/

#print AbstractCompletion.map_id /-
@[simp]
theorem map_id : pkg.map pkg id = id :=
  pkg.map_unique pkg uniformContinuous_id fun a => rfl
#align abstract_completion.map_id AbstractCompletion.map_id
-/

variable {γ : Type _} [UniformSpace γ]

#print AbstractCompletion.extend_map /-
theorem extend_map [CompleteSpace γ] [T0Space γ] {f : β → γ} {g : α → β} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : pkg'.extend f ∘ map g = pkg.extend (f ∘ g) :=
  pkg.funext (pkg'.continuous_extend.comp (pkg.continuous_map pkg' _)) pkg.continuous_extend
    fun a => by rw [pkg.extend_coe (hf.comp hg), comp_app, pkg.map_coe pkg' hg, pkg'.extend_coe hf]
#align abstract_completion.extend_map AbstractCompletion.extend_map
-/

variable (pkg'' : AbstractCompletion γ)

#print AbstractCompletion.map_comp /-
theorem map_comp {g : β → γ} {f : α → β} (hg : UniformContinuous g) (hf : UniformContinuous f) :
    pkg'.map pkg'' g ∘ pkg.map pkg' f = pkg.map pkg'' (g ∘ f) :=
  pkg.extend_map pkg' (pkg''.uniformContinuous_coe.comp hg) hf
#align abstract_completion.map_comp AbstractCompletion.map_comp
-/

end MapSec

section Compare

-- We can now compare two completion packages for the same uniform space
variable (pkg' : AbstractCompletion α)

#print AbstractCompletion.compare /-
/-- The comparison map between two completions of the same uniform space. -/
def compare : pkg.Space → pkg'.Space :=
  pkg.extend pkg'.coe
#align abstract_completion.compare AbstractCompletion.compare
-/

#print AbstractCompletion.uniformContinuous_compare /-
theorem uniformContinuous_compare : UniformContinuous (pkg.compare pkg') :=
  pkg.uniformContinuous_extend
#align abstract_completion.uniform_continuous_compare AbstractCompletion.uniformContinuous_compare
-/

#print AbstractCompletion.compare_coe /-
theorem compare_coe (a : α) : pkg.compare pkg' (pkg.coe a) = pkg'.coe a :=
  pkg.extend_coe pkg'.uniformContinuous_coe a
#align abstract_completion.compare_coe AbstractCompletion.compare_coe
-/

#print AbstractCompletion.inverse_compare /-
theorem inverse_compare : pkg.compare pkg' ∘ pkg'.compare pkg = id :=
  by
  have uc := pkg.uniform_continuous_compare pkg'
  have uc' := pkg'.uniform_continuous_compare pkg
  apply pkg'.funext (uc.comp uc').Continuous continuous_id
  intro a
  rw [comp_app, pkg'.compare_coe pkg, pkg.compare_coe pkg']
  rfl
#align abstract_completion.inverse_compare AbstractCompletion.inverse_compare
-/

#print AbstractCompletion.compareEquiv /-
/-- The uniform bijection between two completions of the same uniform space. -/
def compareEquiv : pkg.Space ≃ᵤ pkg'.Space
    where
  toFun := pkg.compare pkg'
  invFun := pkg'.compare pkg
  left_inv := congr_fun (pkg'.inverse_compare pkg)
  right_inv := congr_fun (pkg.inverse_compare pkg')
  uniformContinuous_toFun := uniformContinuous_compare _ _
  uniformContinuous_invFun := uniformContinuous_compare _ _
#align abstract_completion.compare_equiv AbstractCompletion.compareEquiv
-/

#print AbstractCompletion.uniformContinuous_compareEquiv /-
theorem uniformContinuous_compareEquiv : UniformContinuous (pkg.compareEquiv pkg') :=
  pkg.uniformContinuous_compare pkg'
#align abstract_completion.uniform_continuous_compare_equiv AbstractCompletion.uniformContinuous_compareEquiv
-/

#print AbstractCompletion.uniformContinuous_compareEquiv_symm /-
theorem uniformContinuous_compareEquiv_symm : UniformContinuous (pkg.compareEquiv pkg').symm :=
  pkg'.uniformContinuous_compare pkg
#align abstract_completion.uniform_continuous_compare_equiv_symm AbstractCompletion.uniformContinuous_compareEquiv_symm
-/

end Compare

section Prod

variable (pkg' : AbstractCompletion β)

local notation "hatβ" => pkg'.Space

local notation "ι'" => pkg'.coe

#print AbstractCompletion.prod /-
/-- Products of completions -/
protected def prod : AbstractCompletion (α × β)
    where
  Space := hatα × hatβ
  coe p := ⟨ι p.1, ι' p.2⟩
  uniformStruct := Prod.uniformSpace
  complete := by infer_instance
  separation := by infer_instance
  UniformInducing := UniformInducing.prod pkg.UniformInducing pkg'.UniformInducing
  dense := pkg.dense.map_apply pkg'.dense
#align abstract_completion.prod AbstractCompletion.prod
-/

end Prod

section Extension₂

variable (pkg' : AbstractCompletion β)

local notation "hatβ" => pkg'.Space

local notation "ι'" => pkg'.coe

variable {γ : Type _} [UniformSpace γ]

open Function

#print AbstractCompletion.extend₂ /-
/-- Extend two variable map to completions. -/
protected def extend₂ (f : α → β → γ) : hatα → hatβ → γ :=
  curry <| (pkg.Prod pkg').extend (uncurry f)
#align abstract_completion.extend₂ AbstractCompletion.extend₂
-/

section T0Space

variable [T0Space γ] {f : α → β → γ}

#print AbstractCompletion.extension₂_coe_coe /-
theorem extension₂_coe_coe (hf : UniformContinuous <| uncurry f) (a : α) (b : β) :
    pkg.extend₂ pkg' f (ι a) (ι' b) = f a b :=
  show (pkg.Prod pkg').extend (uncurry f) ((pkg.Prod pkg').coe (a, b)) = uncurry f (a, b) from
    (pkg.Prod pkg').extend_coe hf _
#align abstract_completion.extension₂_coe_coe AbstractCompletion.extension₂_coe_coe
-/

end T0Space

variable {f : α → β → γ}

variable [CompleteSpace γ] (f)

#print AbstractCompletion.uniformContinuous_extension₂ /-
theorem uniformContinuous_extension₂ : UniformContinuous₂ (pkg.extend₂ pkg' f) :=
  by
  rw [uniformContinuous₂_def, AbstractCompletion.extend₂, uncurry_curry]
  apply uniform_continuous_extend
#align abstract_completion.uniform_continuous_extension₂ AbstractCompletion.uniformContinuous_extension₂
-/

end Extension₂

section Map₂

variable (pkg' : AbstractCompletion β)

local notation "hatβ" => pkg'.Space

local notation "ι'" => pkg'.coe

variable {γ : Type _} [UniformSpace γ] (pkg'' : AbstractCompletion γ)

local notation "hatγ" => pkg''.Space

local notation "ι''" => pkg''.coe

local notation f " ∘₂ " g => bicompr f g

#print AbstractCompletion.map₂ /-
/-- Lift two variable maps to completions. -/
protected def map₂ (f : α → β → γ) : hatα → hatβ → hatγ :=
  pkg.extend₂ pkg' (pkg''.coe ∘₂ f)
#align abstract_completion.map₂ AbstractCompletion.map₂
-/

#print AbstractCompletion.uniformContinuous_map₂ /-
theorem uniformContinuous_map₂ (f : α → β → γ) : UniformContinuous₂ (pkg.zipWith pkg' pkg'' f) :=
  pkg.uniformContinuous_extension₂ pkg' _
#align abstract_completion.uniform_continuous_map₂ AbstractCompletion.uniformContinuous_map₂
-/

#print AbstractCompletion.continuous_map₂ /-
theorem continuous_map₂ {δ} [TopologicalSpace δ] {f : α → β → γ} {a : δ → hatα} {b : δ → hatβ}
    (ha : Continuous a) (hb : Continuous b) :
    Continuous fun d : δ => pkg.zipWith pkg' pkg'' f (a d) (b d) :=
  ((pkg.uniformContinuous_map₂ pkg' pkg'' f).Continuous.comp (Continuous.prod_mk ha hb) : _)
#align abstract_completion.continuous_map₂ AbstractCompletion.continuous_map₂
-/

#print AbstractCompletion.map₂_coe_coe /-
theorem map₂_coe_coe (a : α) (b : β) (f : α → β → γ) (hf : UniformContinuous₂ f) :
    pkg.zipWith pkg' pkg'' f (ι a) (ι' b) = ι'' (f a b) :=
  pkg.extension₂_coe_coe pkg' (pkg''.uniformContinuous_coe.comp hf) a b
#align abstract_completion.map₂_coe_coe AbstractCompletion.map₂_coe_coe
-/

end Map₂

end AbstractCompletion

