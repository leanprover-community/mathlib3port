/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.uniform_space.abstract_completion
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UniformSpace.UniformEmbedding
import Mathbin.Topology.UniformSpace.Equiv

/-!
# Abstract theory of Hausdorff completions of uniform spaces

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
identify the results of any two constructions that lead to something one could reasonnably
call a completion.

## Tags

uniform spaces, completion, universal property
-/


noncomputable section

attribute [local instance] Classical.propDecidable

open Filter Set Function

universe u

/-- A completion of `α` is the data of a complete separated uniform space (from the same universe)
and a map from `α` with dense range and inducing the original uniform structure on `α`. -/
structure AbstractCompletion (α : Type u) [UniformSpace α] where
  Space : Type u
  coe : α → space
  uniformStruct : UniformSpace space
  complete : CompleteSpace space
  separation : SeparatedSpace space
  UniformInducing : UniformInducing coe
  dense : DenseRange coe
#align abstract_completion AbstractCompletion

attribute [local instance]
  AbstractCompletion.uniformStruct AbstractCompletion.complete AbstractCompletion.separation

namespace AbstractCompletion

variable {α : Type _} [UniformSpace α] (pkg : AbstractCompletion α)

-- mathport name: exprhatα
local notation "hatα" => pkg.Space

-- mathport name: exprι
local notation "ι" => pkg.coe

/-- If `α` is complete, then it is an abstract completion of itself. -/
def ofComplete [SeparatedSpace α] [CompleteSpace α] : AbstractCompletion α :=
  mk α id inferInstance inferInstance inferInstance uniform_inducing_id dense_range_id
#align abstract_completion.of_complete AbstractCompletion.ofComplete

theorem closure_range : closure (range ι) = univ :=
  pkg.dense.closure_range
#align abstract_completion.closure_range AbstractCompletion.closure_range

theorem dense_inducing : DenseInducing ι :=
  ⟨pkg.UniformInducing.Inducing, pkg.dense⟩
#align abstract_completion.dense_inducing AbstractCompletion.dense_inducing

theorem uniform_continuous_coe : UniformContinuous ι :=
  UniformInducing.uniform_continuous pkg.UniformInducing
#align abstract_completion.uniform_continuous_coe AbstractCompletion.uniform_continuous_coe

theorem continuous_coe : Continuous ι :=
  pkg.uniform_continuous_coe.Continuous
#align abstract_completion.continuous_coe AbstractCompletion.continuous_coe

@[elab_as_elim]
theorem induction_on {p : hatα → Prop} (a : hatα) (hp : IsClosed { a | p a }) (ih : ∀ a, p (ι a)) :
    p a :=
  is_closed_property pkg.dense hp ih a
#align abstract_completion.induction_on AbstractCompletion.induction_on

variable {β : Type _}

protected theorem funext [TopologicalSpace β] [T2Space β] {f g : hatα → β} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ a, f (ι a) = g (ι a)) : f = g :=
  funext fun a => pkg.induction_on a (is_closed_eq hf hg) h
#align abstract_completion.funext AbstractCompletion.funext

variable [UniformSpace β]

section Extend

/-- Extension of maps to completions -/
protected def extend (f : α → β) : hatα → β :=
  if UniformContinuous f then pkg.DenseInducing.extend f else fun x => f (pkg.dense.some x)
#align abstract_completion.extend AbstractCompletion.extend

variable {f : α → β}

theorem extend_def (hf : UniformContinuous f) : pkg.extend f = pkg.DenseInducing.extend f :=
  if_pos hf
#align abstract_completion.extend_def AbstractCompletion.extend_def

theorem extend_coe [T2Space β] (hf : UniformContinuous f) (a : α) : (pkg.extend f) (ι a) = f a :=
  by
  rw [pkg.extend_def hf]
  exact pkg.dense_inducing.extend_eq hf.continuous a
#align abstract_completion.extend_coe AbstractCompletion.extend_coe

variable [CompleteSpace β]

theorem uniform_continuous_extend : UniformContinuous (pkg.extend f) :=
  by
  by_cases hf : UniformContinuous f
  · rw [pkg.extend_def hf]
    exact uniform_continuous_uniformly_extend pkg.uniform_inducing pkg.dense hf
  · change UniformContinuous (ite _ _ _)
    rw [if_neg hf]
    exact uniform_continuous_of_const fun a b => by congr
#align abstract_completion.uniform_continuous_extend AbstractCompletion.uniform_continuous_extend

theorem continuous_extend : Continuous (pkg.extend f) :=
  pkg.uniform_continuous_extend.Continuous
#align abstract_completion.continuous_extend AbstractCompletion.continuous_extend

variable [SeparatedSpace β]

theorem extend_unique (hf : UniformContinuous f) {g : hatα → β} (hg : UniformContinuous g)
    (h : ∀ a : α, f a = g (ι a)) : pkg.extend f = g :=
  by
  apply pkg.funext pkg.continuous_extend hg.continuous
  simpa only [pkg.extend_coe hf] using h
#align abstract_completion.extend_unique AbstractCompletion.extend_unique

@[simp]
theorem extend_comp_coe {f : hatα → β} (hf : UniformContinuous f) : pkg.extend (f ∘ ι) = f :=
  funext fun x =>
    pkg.induction_on x (is_closed_eq pkg.continuous_extend hf.Continuous) fun y =>
      pkg.extend_coe (hf.comp <| pkg.uniform_continuous_coe) y
#align abstract_completion.extend_comp_coe AbstractCompletion.extend_comp_coe

end Extend

section MapSec

variable (pkg' : AbstractCompletion β)

-- mathport name: exprhatβ
local notation "hatβ" => pkg'.Space

-- mathport name: exprι'
local notation "ι'" => pkg'.coe

/-- Lifting maps to completions -/
protected def map (f : α → β) : hatα → hatβ :=
  pkg.extend (ι' ∘ f)
#align abstract_completion.map AbstractCompletion.map

-- mathport name: exprmap
local notation "map" => pkg.map pkg'

variable (f : α → β)

theorem uniform_continuous_map : UniformContinuous (map f) :=
  pkg.uniform_continuous_extend
#align abstract_completion.uniform_continuous_map AbstractCompletion.uniform_continuous_map

theorem continuous_map : Continuous (map f) :=
  pkg.continuous_extend
#align abstract_completion.continuous_map AbstractCompletion.continuous_map

variable {f}

@[simp]
theorem map_coe (hf : UniformContinuous f) (a : α) : map f (ι a) = ι' (f a) :=
  pkg.extend_coe (pkg'.uniform_continuous_coe.comp hf) a
#align abstract_completion.map_coe AbstractCompletion.map_coe

theorem map_unique {f : α → β} {g : hatα → hatβ} (hg : UniformContinuous g)
    (h : ∀ a, ι' (f a) = g (ι a)) : map f = g :=
  pkg.funext (pkg.continuous_map _ _) hg.Continuous <|
    by
    intro a
    change pkg.extend (ι' ∘ f) _ = _
    simp only [(· ∘ ·), h]
    rw [pkg.extend_coe (hg.comp pkg.uniform_continuous_coe)]
#align abstract_completion.map_unique AbstractCompletion.map_unique

@[simp]
theorem map_id : pkg.map pkg id = id :=
  pkg.map_unique pkg uniform_continuous_id fun a => rfl
#align abstract_completion.map_id AbstractCompletion.map_id

variable {γ : Type _} [UniformSpace γ]

theorem extend_map [CompleteSpace γ] [SeparatedSpace γ] {f : β → γ} {g : α → β}
    (hf : UniformContinuous f) (hg : UniformContinuous g) :
    pkg'.extend f ∘ map g = pkg.extend (f ∘ g) :=
  (pkg.funext (pkg'.continuous_extend.comp (pkg.continuous_map pkg' _)) pkg.continuous_extend)
    fun a => by rw [pkg.extend_coe (hf.comp hg), comp_app, pkg.map_coe pkg' hg, pkg'.extend_coe hf]
#align abstract_completion.extend_map AbstractCompletion.extend_map

variable (pkg'' : AbstractCompletion γ)

theorem map_comp {g : β → γ} {f : α → β} (hg : UniformContinuous g) (hf : UniformContinuous f) :
    pkg'.map pkg'' g ∘ pkg.map pkg' f = pkg.map pkg'' (g ∘ f) :=
  pkg.extend_map pkg' (pkg''.uniform_continuous_coe.comp hg) hf
#align abstract_completion.map_comp AbstractCompletion.map_comp

end MapSec

section Compare

-- We can now compare two completion packages for the same uniform space
variable (pkg' : AbstractCompletion α)

/-- The comparison map between two completions of the same uniform space. -/
def compare : pkg.Space → pkg'.Space :=
  pkg.extend pkg'.coe
#align abstract_completion.compare AbstractCompletion.compare

theorem uniform_continuous_compare : UniformContinuous (pkg.compare pkg') :=
  pkg.uniform_continuous_extend
#align abstract_completion.uniform_continuous_compare AbstractCompletion.uniform_continuous_compare

theorem compare_coe (a : α) : pkg.compare pkg' (pkg.coe a) = pkg'.coe a :=
  pkg.extend_coe pkg'.uniform_continuous_coe a
#align abstract_completion.compare_coe AbstractCompletion.compare_coe

theorem inverse_compare : pkg.compare pkg' ∘ pkg'.compare pkg = id :=
  by
  have uc := pkg.uniform_continuous_compare pkg'
  have uc' := pkg'.uniform_continuous_compare pkg
  apply pkg'.funext (uc.comp uc').Continuous continuous_id
  intro a
  rw [comp_app, pkg'.compare_coe pkg, pkg.compare_coe pkg']
  rfl
#align abstract_completion.inverse_compare AbstractCompletion.inverse_compare

/-- The uniform bijection between two completions of the same uniform space. -/
def compareEquiv : pkg.Space ≃ᵤ pkg'.Space
    where
  toFun := pkg.compare pkg'
  invFun := pkg'.compare pkg
  left_inv := congr_fun (pkg'.inverse_compare pkg)
  right_inv := congr_fun (pkg.inverse_compare pkg')
  uniform_continuous_to_fun := uniform_continuous_compare _ _
  uniform_continuous_inv_fun := uniform_continuous_compare _ _
#align abstract_completion.compare_equiv AbstractCompletion.compareEquiv

theorem uniform_continuous_compare_equiv : UniformContinuous (pkg.compareEquiv pkg') :=
  pkg.uniform_continuous_compare pkg'
#align
  abstract_completion.uniform_continuous_compare_equiv AbstractCompletion.uniform_continuous_compare_equiv

theorem uniform_continuous_compare_equiv_symm : UniformContinuous (pkg.compareEquiv pkg').symm :=
  pkg'.uniform_continuous_compare pkg
#align
  abstract_completion.uniform_continuous_compare_equiv_symm AbstractCompletion.uniform_continuous_compare_equiv_symm

end Compare

section Prod

variable (pkg' : AbstractCompletion β)

-- mathport name: exprhatβ
local notation "hatβ" => pkg'.Space

-- mathport name: exprι'
local notation "ι'" => pkg'.coe

/-- Products of completions -/
protected def prod : AbstractCompletion (α × β)
    where
  Space := hatα × hatβ
  coe p := ⟨ι p.1, ι' p.2⟩
  uniformStruct := Prod.uniformSpace
  complete := by infer_instance
  separation := by infer_instance
  UniformInducing := UniformInducing.prod pkg.UniformInducing pkg'.UniformInducing
  dense := pkg.dense.prod_map pkg'.dense
#align abstract_completion.prod AbstractCompletion.prod

end Prod

section Extension₂

variable (pkg' : AbstractCompletion β)

-- mathport name: exprhatβ
local notation "hatβ" => pkg'.Space

-- mathport name: exprι'
local notation "ι'" => pkg'.coe

variable {γ : Type _} [UniformSpace γ]

open Function

/-- Extend two variable map to completions. -/
protected def extend₂ (f : α → β → γ) : hatα → hatβ → γ :=
  curry <| (pkg.Prod pkg').extend (uncurry f)
#align abstract_completion.extend₂ AbstractCompletion.extend₂

section SeparatedSpace

variable [SeparatedSpace γ] {f : α → β → γ}

theorem extension₂_coe_coe (hf : UniformContinuous <| uncurry f) (a : α) (b : β) :
    pkg.extend₂ pkg' f (ι a) (ι' b) = f a b :=
  show (pkg.Prod pkg').extend (uncurry f) ((pkg.Prod pkg').coe (a, b)) = uncurry f (a, b) from
    (pkg.Prod pkg').extend_coe hf _
#align abstract_completion.extension₂_coe_coe AbstractCompletion.extension₂_coe_coe

end SeparatedSpace

variable {f : α → β → γ}

variable [CompleteSpace γ] (f)

theorem uniform_continuous_extension₂ : UniformContinuous₂ (pkg.extend₂ pkg' f) :=
  by
  rw [uniform_continuous₂_def, AbstractCompletion.extend₂, uncurry_curry]
  apply uniform_continuous_extend
#align
  abstract_completion.uniform_continuous_extension₂ AbstractCompletion.uniform_continuous_extension₂

end Extension₂

section Map₂

variable (pkg' : AbstractCompletion β)

-- mathport name: exprhatβ
local notation "hatβ" => pkg'.Space

-- mathport name: exprι'
local notation "ι'" => pkg'.coe

variable {γ : Type _} [UniformSpace γ] (pkg'' : AbstractCompletion γ)

-- mathport name: exprhatγ
local notation "hatγ" => pkg''.Space

-- mathport name: exprι''
local notation "ι''" => pkg''.coe

-- mathport name: «expr ∘₂ »
local notation f " ∘₂ " g => bicompr f g

/-- Lift two variable maps to completions. -/
protected def map₂ (f : α → β → γ) : hatα → hatβ → hatγ :=
  pkg.extend₂ pkg' (pkg''.coe ∘₂ f)
#align abstract_completion.map₂ AbstractCompletion.map₂

theorem uniform_continuous_map₂ (f : α → β → γ) : UniformContinuous₂ (pkg.map₂ pkg' pkg'' f) :=
  pkg.uniform_continuous_extension₂ pkg' _
#align abstract_completion.uniform_continuous_map₂ AbstractCompletion.uniform_continuous_map₂

theorem continuous_map₂ {δ} [TopologicalSpace δ] {f : α → β → γ} {a : δ → hatα} {b : δ → hatβ}
    (ha : Continuous a) (hb : Continuous b) :
    Continuous fun d : δ => pkg.map₂ pkg' pkg'' f (a d) (b d) :=
  ((pkg.uniform_continuous_map₂ pkg' pkg'' f).Continuous.comp (Continuous.prod_mk ha hb) : _)
#align abstract_completion.continuous_map₂ AbstractCompletion.continuous_map₂

theorem map₂_coe_coe (a : α) (b : β) (f : α → β → γ) (hf : UniformContinuous₂ f) :
    pkg.map₂ pkg' pkg'' f (ι a) (ι' b) = ι'' (f a b) :=
  pkg.extension₂_coe_coe pkg' (pkg''.uniform_continuous_coe.comp hf) a b
#align abstract_completion.map₂_coe_coe AbstractCompletion.map₂_coe_coe

end Map₂

end AbstractCompletion

