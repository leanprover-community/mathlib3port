/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
import Data.Set.Prod
import Logic.Function.Conjugate

#align_import data.set.function from "leanprover-community/mathlib"@"f974ae84dfc9fea6a036a8f30f09414254e3bc40"

/-!
# Functions over sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

### Predicate

* `set.eq_on f₁ f₂ s` : functions `f₁` and `f₂` are equal at every point of `s`;
* `set.maps_to f s t` : `f` sends every point of `s` to a point of `t`;
* `set.inj_on f s` : restriction of `f` to `s` is injective;
* `set.surj_on f s t` : every point in `s` has a preimage in `s`;
* `set.bij_on f s t` : `f` is a bijection between `s` and `t`;
* `set.left_inv_on f' f s` : for every `x ∈ s` we have `f' (f x) = x`;
* `set.right_inv_on f' f t` : for every `y ∈ t` we have `f (f' y) = y`;
* `set.inv_on f' f s t` : `f'` is a two-side inverse of `f` on `s` and `t`, i.e.
  we have `set.left_inv_on f' f s` and `set.right_inv_on f' f t`.

### Functions

* `set.restrict f s` : restrict the domain of `f` to the set `s`;
* `set.cod_restrict f s h` : given `h : ∀ x, f x ∈ s`, restrict the codomain of `f` to the set `s`;
* `set.maps_to.restrict f s t h`: given `h : maps_to f s t`, restrict the domain of `f` to `s`
  and the codomain to `t`.
-/


universe u v w x y

variable {α : Type u} {β : Type v} {π : α → Type v} {γ : Type w} {ι : Sort x}

open Equiv Equiv.Perm Function

namespace Set

/-! ### Restrict -/


#print Set.restrict /-
/-- Restrict domain of a function `f` to a set `s`. Same as `subtype.restrict` but this version
takes an argument `↥s` instead of `subtype s`. -/
def restrict (s : Set α) (f : ∀ a : α, π a) : ∀ a : s, π a := fun x => f x
#align set.restrict Set.restrict
-/

#print Set.restrict_eq /-
theorem restrict_eq (f : α → β) (s : Set α) : s.restrict f = f ∘ coe :=
  rfl
#align set.restrict_eq Set.restrict_eq
-/

#print Set.restrict_apply /-
@[simp]
theorem restrict_apply (f : α → β) (s : Set α) (x : s) : s.restrict f x = f x :=
  rfl
#align set.restrict_apply Set.restrict_apply
-/

#print Set.restrict_eq_iff /-
theorem restrict_eq_iff {f : ∀ a, π a} {s : Set α} {g : ∀ a : s, π a} :
    restrict s f = g ↔ ∀ (a) (ha : a ∈ s), f a = g ⟨a, ha⟩ :=
  funext_iff.trans Subtype.forall
#align set.restrict_eq_iff Set.restrict_eq_iff
-/

#print Set.eq_restrict_iff /-
theorem eq_restrict_iff {s : Set α} {f : ∀ a : s, π a} {g : ∀ a, π a} :
    f = restrict s g ↔ ∀ (a) (ha : a ∈ s), f ⟨a, ha⟩ = g a :=
  funext_iff.trans Subtype.forall
#align set.eq_restrict_iff Set.eq_restrict_iff
-/

#print Set.range_restrict /-
@[simp]
theorem range_restrict (f : α → β) (s : Set α) : Set.range (s.restrict f) = f '' s :=
  (range_comp _ _).trans <| congr_arg ((· '' ·) f) Subtype.range_coe
#align set.range_restrict Set.range_restrict
-/

#print Set.image_restrict /-
theorem image_restrict (f : α → β) (s t : Set α) : s.restrict f '' (coe ⁻¹' t) = f '' (t ∩ s) := by
  rw [restrict, image_comp, image_preimage_eq_inter_range, Subtype.range_coe]
#align set.image_restrict Set.image_restrict
-/

/- ././././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (a «expr ∉ » s) -/
#print Set.restrict_dite /-
@[simp]
theorem restrict_dite {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀ a ∈ s, β)
    (g : ∀ (a) (_ : a ∉ s), β) :
    (s.restrict fun a => if h : a ∈ s then f a h else g a h) = fun a => f a a.2 :=
  funext fun a => dif_pos a.2
#align set.restrict_dite Set.restrict_dite
-/

/- ././././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (a «expr ∉ » s) -/
#print Set.restrict_dite_compl /-
@[simp]
theorem restrict_dite_compl {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀ a ∈ s, β)
    (g : ∀ (a) (_ : a ∉ s), β) :
    (sᶜ.restrict fun a => if h : a ∈ s then f a h else g a h) = fun a => g a a.2 :=
  funext fun a => dif_neg a.2
#align set.restrict_dite_compl Set.restrict_dite_compl
-/

#print Set.restrict_ite /-
@[simp]
theorem restrict_ite (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    (s.restrict fun a => if a ∈ s then f a else g a) = s.restrict f :=
  restrict_dite _ _
#align set.restrict_ite Set.restrict_ite
-/

#print Set.restrict_ite_compl /-
@[simp]
theorem restrict_ite_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    (sᶜ.restrict fun a => if a ∈ s then f a else g a) = sᶜ.restrict g :=
  restrict_dite_compl _ _
#align set.restrict_ite_compl Set.restrict_ite_compl
-/

#print Set.restrict_piecewise /-
@[simp]
theorem restrict_piecewise (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    s.restrict (piecewise s f g) = s.restrict f :=
  restrict_ite _ _ _
#align set.restrict_piecewise Set.restrict_piecewise
-/

#print Set.restrict_piecewise_compl /-
@[simp]
theorem restrict_piecewise_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    sᶜ.restrict (piecewise s f g) = sᶜ.restrict g :=
  restrict_ite_compl _ _ _
#align set.restrict_piecewise_compl Set.restrict_piecewise_compl
-/

#print Set.restrict_extend_range /-
theorem restrict_extend_range (f : α → β) (g : α → γ) (g' : β → γ) :
    (range f).restrict (extend f g g') = fun x => g x.coe_prop.some := by convert restrict_dite _ _
#align set.restrict_extend_range Set.restrict_extend_range
-/

#print Set.restrict_extend_compl_range /-
@[simp]
theorem restrict_extend_compl_range (f : α → β) (g : α → γ) (g' : β → γ) :
    range fᶜ.restrict (extend f g g') = g' ∘ coe := by convert restrict_dite_compl _ _
#align set.restrict_extend_compl_range Set.restrict_extend_compl_range
-/

#print Set.range_extend_subset /-
theorem range_extend_subset (f : α → β) (g : α → γ) (g' : β → γ) :
    range (extend f g g') ⊆ range g ∪ g' '' range fᶜ := by
  classical
  rintro _ ⟨y, rfl⟩
  rw [extend_def]
  split_ifs
  exacts [Or.inl (mem_range_self _), Or.inr (mem_image_of_mem _ h)]
#align set.range_extend_subset Set.range_extend_subset
-/

#print Set.range_extend /-
theorem range_extend {f : α → β} (hf : Injective f) (g : α → γ) (g' : β → γ) :
    range (extend f g g') = range g ∪ g' '' range fᶜ :=
  by
  refine' (range_extend_subset _ _ _).antisymm _
  rintro z (⟨x, rfl⟩ | ⟨y, hy, rfl⟩)
  exacts [⟨f x, hf.extend_apply _ _ _⟩, ⟨y, extend_apply' _ _ _ hy⟩]
#align set.range_extend Set.range_extend
-/

#print Set.codRestrict /-
/-- Restrict codomain of a function `f` to a set `s`. Same as `subtype.coind` but this version
has codomain `↥s` instead of `subtype s`. -/
def codRestrict (f : ι → α) (s : Set α) (h : ∀ x, f x ∈ s) : ι → s := fun x => ⟨f x, h x⟩
#align set.cod_restrict Set.codRestrict
-/

#print Set.val_codRestrict_apply /-
@[simp]
theorem val_codRestrict_apply (f : ι → α) (s : Set α) (h : ∀ x, f x ∈ s) (x : ι) :
    (codRestrict f s h x : α) = f x :=
  rfl
#align set.coe_cod_restrict_apply Set.val_codRestrict_apply
-/

#print Set.restrict_comp_codRestrict /-
@[simp]
theorem restrict_comp_codRestrict {f : ι → α} {g : α → β} {b : Set α} (h : ∀ x, f x ∈ b) :
    b.restrict g ∘ b.codRestrict f h = g ∘ f :=
  rfl
#align set.restrict_comp_cod_restrict Set.restrict_comp_codRestrict
-/

#print Set.injective_codRestrict /-
@[simp]
theorem injective_codRestrict {f : ι → α} {s : Set α} (h : ∀ x, f x ∈ s) :
    Injective (codRestrict f s h) ↔ Injective f := by
  simp only [injective, Subtype.ext_iff, coe_cod_restrict_apply]
#align set.injective_cod_restrict Set.injective_codRestrict
-/

alias ⟨_, _root_.function.injective.cod_restrict⟩ := injective_cod_restrict
#align function.injective.cod_restrict Function.Injective.codRestrict

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {p : Set γ} {f f₁ f₂ f₃ : α → β} {g g₁ g₂ : β → γ}
  {f' f₁' f₂' : β → α} {g' : γ → β} {a : α} {b : β}

/-! ### Equality on a set -/


#print Set.EqOn /-
/-- Two functions `f₁ f₂ : α → β` are equal on `s`
  if `f₁ x = f₂ x` for all `x ∈ a`. -/
def EqOn (f₁ f₂ : α → β) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x
#align set.eq_on Set.EqOn
-/

#print Set.eqOn_empty /-
@[simp]
theorem eqOn_empty (f₁ f₂ : α → β) : EqOn f₁ f₂ ∅ := fun x => False.elim
#align set.eq_on_empty Set.eqOn_empty
-/

#print Set.eqOn_singleton /-
@[simp]
theorem eqOn_singleton : EqOn f₁ f₂ {a} ↔ f₁ a = f₂ a := by simp [Set.EqOn]
#align set.eq_on_singleton Set.eqOn_singleton
-/

#print Set.restrict_eq_restrict_iff /-
@[simp]
theorem restrict_eq_restrict_iff : restrict s f₁ = restrict s f₂ ↔ EqOn f₁ f₂ s :=
  restrict_eq_iff
#align set.restrict_eq_restrict_iff Set.restrict_eq_restrict_iff
-/

#print Set.EqOn.symm /-
@[symm]
theorem EqOn.symm (h : EqOn f₁ f₂ s) : EqOn f₂ f₁ s := fun x hx => (h hx).symm
#align set.eq_on.symm Set.EqOn.symm
-/

#print Set.eqOn_comm /-
theorem eqOn_comm : EqOn f₁ f₂ s ↔ EqOn f₂ f₁ s :=
  ⟨EqOn.symm, EqOn.symm⟩
#align set.eq_on_comm Set.eqOn_comm
-/

#print Set.eqOn_refl /-
@[refl]
theorem eqOn_refl (f : α → β) (s : Set α) : EqOn f f s := fun _ _ => rfl
#align set.eq_on_refl Set.eqOn_refl
-/

#print Set.EqOn.trans /-
@[trans]
theorem EqOn.trans (h₁ : EqOn f₁ f₂ s) (h₂ : EqOn f₂ f₃ s) : EqOn f₁ f₃ s := fun x hx =>
  (h₁ hx).trans (h₂ hx)
#align set.eq_on.trans Set.EqOn.trans
-/

#print Set.EqOn.image_eq /-
theorem EqOn.image_eq (heq : EqOn f₁ f₂ s) : f₁ '' s = f₂ '' s :=
  image_congr HEq
#align set.eq_on.image_eq Set.EqOn.image_eq
-/

#print Set.EqOn.inter_preimage_eq /-
theorem EqOn.inter_preimage_eq (heq : EqOn f₁ f₂ s) (t : Set β) : s ∩ f₁ ⁻¹' t = s ∩ f₂ ⁻¹' t :=
  ext fun x => and_congr_right_iff.2 fun hx => by rw [mem_preimage, mem_preimage, HEq hx]
#align set.eq_on.inter_preimage_eq Set.EqOn.inter_preimage_eq
-/

#print Set.EqOn.mono /-
theorem EqOn.mono (hs : s₁ ⊆ s₂) (hf : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ s₁ := fun x hx => hf (hs hx)
#align set.eq_on.mono Set.EqOn.mono
-/

#print Set.eqOn_union /-
@[simp]
theorem eqOn_union : EqOn f₁ f₂ (s₁ ∪ s₂) ↔ EqOn f₁ f₂ s₁ ∧ EqOn f₁ f₂ s₂ :=
  forall₂_or_left
#align set.eq_on_union Set.eqOn_union
-/

#print Set.EqOn.union /-
theorem EqOn.union (h₁ : EqOn f₁ f₂ s₁) (h₂ : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ (s₁ ∪ s₂) :=
  eqOn_union.2 ⟨h₁, h₂⟩
#align set.eq_on.union Set.EqOn.union
-/

#print Set.EqOn.comp_left /-
theorem EqOn.comp_left (h : s.EqOn f₁ f₂) : s.EqOn (g ∘ f₁) (g ∘ f₂) := fun a ha =>
  congr_arg _ <| h ha
#align set.eq_on.comp_left Set.EqOn.comp_left
-/

#print Set.eqOn_range /-
@[simp]
theorem eqOn_range {ι : Sort _} {f : ι → α} {g₁ g₂ : α → β} :
    EqOn g₁ g₂ (range f) ↔ g₁ ∘ f = g₂ ∘ f :=
  forall_mem_range.trans <| funext_iff.symm
#align set.eq_on_range Set.eqOn_range
-/

alias ⟨eq_on.comp_eq, _⟩ := eq_on_range
#align set.eq_on.comp_eq Set.EqOn.comp_eq

/-! ### Congruence lemmas -/


section Order

variable [Preorder α] [Preorder β]

#print MonotoneOn.congr /-
theorem MonotoneOn.congr (h₁ : MonotoneOn f₁ s) (h : s.EqOn f₁ f₂) : MonotoneOn f₂ s :=
  by
  intro a ha b hb hab
  rw [← h ha, ← h hb]
  exact h₁ ha hb hab
#align monotone_on.congr MonotoneOn.congr
-/

#print AntitoneOn.congr /-
theorem AntitoneOn.congr (h₁ : AntitoneOn f₁ s) (h : s.EqOn f₁ f₂) : AntitoneOn f₂ s :=
  h₁.dual_right.congr h
#align antitone_on.congr AntitoneOn.congr
-/

#print StrictMonoOn.congr /-
theorem StrictMonoOn.congr (h₁ : StrictMonoOn f₁ s) (h : s.EqOn f₁ f₂) : StrictMonoOn f₂ s :=
  by
  intro a ha b hb hab
  rw [← h ha, ← h hb]
  exact h₁ ha hb hab
#align strict_mono_on.congr StrictMonoOn.congr
-/

#print StrictAntiOn.congr /-
theorem StrictAntiOn.congr (h₁ : StrictAntiOn f₁ s) (h : s.EqOn f₁ f₂) : StrictAntiOn f₂ s :=
  h₁.dual_right.congr h
#align strict_anti_on.congr StrictAntiOn.congr
-/

#print Set.EqOn.congr_monotoneOn /-
theorem EqOn.congr_monotoneOn (h : s.EqOn f₁ f₂) : MonotoneOn f₁ s ↔ MonotoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_monotone_on Set.EqOn.congr_monotoneOn
-/

#print Set.EqOn.congr_antitoneOn /-
theorem EqOn.congr_antitoneOn (h : s.EqOn f₁ f₂) : AntitoneOn f₁ s ↔ AntitoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_antitone_on Set.EqOn.congr_antitoneOn
-/

#print Set.EqOn.congr_strictMonoOn /-
theorem EqOn.congr_strictMonoOn (h : s.EqOn f₁ f₂) : StrictMonoOn f₁ s ↔ StrictMonoOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_strict_mono_on Set.EqOn.congr_strictMonoOn
-/

#print Set.EqOn.congr_strictAntiOn /-
theorem EqOn.congr_strictAntiOn (h : s.EqOn f₁ f₂) : StrictAntiOn f₁ s ↔ StrictAntiOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
#align set.eq_on.congr_strict_anti_on Set.EqOn.congr_strictAntiOn
-/

end Order

/-! ### Mono lemmas-/


section Mono

variable [Preorder α] [Preorder β]

#print MonotoneOn.mono /-
theorem MonotoneOn.mono (h : MonotoneOn f s) (h' : s₂ ⊆ s) : MonotoneOn f s₂ := fun x hx y hy =>
  h (h' hx) (h' hy)
#align monotone_on.mono MonotoneOn.mono
-/

#print AntitoneOn.mono /-
theorem AntitoneOn.mono (h : AntitoneOn f s) (h' : s₂ ⊆ s) : AntitoneOn f s₂ := fun x hx y hy =>
  h (h' hx) (h' hy)
#align antitone_on.mono AntitoneOn.mono
-/

#print StrictMonoOn.mono /-
theorem StrictMonoOn.mono (h : StrictMonoOn f s) (h' : s₂ ⊆ s) : StrictMonoOn f s₂ :=
  fun x hx y hy => h (h' hx) (h' hy)
#align strict_mono_on.mono StrictMonoOn.mono
-/

#print StrictAntiOn.mono /-
theorem StrictAntiOn.mono (h : StrictAntiOn f s) (h' : s₂ ⊆ s) : StrictAntiOn f s₂ :=
  fun x hx y hy => h (h' hx) (h' hy)
#align strict_anti_on.mono StrictAntiOn.mono
-/

#print MonotoneOn.monotone /-
protected theorem MonotoneOn.monotone (h : MonotoneOn f s) : Monotone (f ∘ coe : s → β) :=
  fun x y hle => h x.coe_prop y.coe_prop hle
#align monotone_on.monotone MonotoneOn.monotone
-/

#print AntitoneOn.monotone /-
protected theorem AntitoneOn.monotone (h : AntitoneOn f s) : Antitone (f ∘ coe : s → β) :=
  fun x y hle => h x.coe_prop y.coe_prop hle
#align antitone_on.monotone AntitoneOn.monotone
-/

#print StrictMonoOn.strictMono /-
protected theorem StrictMonoOn.strictMono (h : StrictMonoOn f s) : StrictMono (f ∘ coe : s → β) :=
  fun x y hlt => h x.coe_prop y.coe_prop hlt
#align strict_mono_on.strict_mono StrictMonoOn.strictMono
-/

#print StrictAntiOn.strictAnti /-
protected theorem StrictAntiOn.strictAnti (h : StrictAntiOn f s) : StrictAnti (f ∘ coe : s → β) :=
  fun x y hlt => h x.coe_prop y.coe_prop hlt
#align strict_anti_on.strict_anti StrictAntiOn.strictAnti
-/

end Mono

/-! ### maps to -/


#print Set.MapsTo /-
/-- `maps_to f a b` means that the image of `a` is contained in `b`. -/
def MapsTo (f : α → β) (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f x ∈ t
#align set.maps_to Set.MapsTo
-/

#print Set.MapsTo.restrict /-
/-- Given a map `f` sending `s : set α` into `t : set β`, restrict domain of `f` to `s`
and the codomain to `t`. Same as `subtype.map`. -/
def MapsTo.restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) : s → t :=
  Subtype.map f h
#align set.maps_to.restrict Set.MapsTo.restrict
-/

#print Set.MapsTo.val_restrict_apply /-
@[simp]
theorem MapsTo.val_restrict_apply (h : MapsTo f s t) (x : s) : (h.restrict f s t x : β) = f x :=
  rfl
#align set.maps_to.coe_restrict_apply Set.MapsTo.val_restrict_apply
-/

#print Set.codRestrict_restrict /-
/-- Restricting the domain and then the codomain is the same as `maps_to.restrict`. -/
@[simp]
theorem codRestrict_restrict (h : ∀ x : s, f x ∈ t) :
    codRestrict (s.restrict f) t h = MapsTo.restrict f s t fun x hx => h ⟨x, hx⟩ :=
  rfl
#align set.cod_restrict_restrict Set.codRestrict_restrict
-/

#print Set.MapsTo.restrict_eq_codRestrict /-
/-- Reverse of `set.cod_restrict_restrict`. -/
theorem MapsTo.restrict_eq_codRestrict (h : MapsTo f s t) :
    h.restrict f s t = codRestrict (s.restrict f) t fun x => h x.2 :=
  rfl
#align set.maps_to.restrict_eq_cod_restrict Set.MapsTo.restrict_eq_codRestrict
-/

#print Set.MapsTo.coe_restrict /-
theorem MapsTo.coe_restrict (h : Set.MapsTo f s t) : coe ∘ h.restrict f s t = s.restrict f :=
  rfl
#align set.maps_to.coe_restrict Set.MapsTo.coe_restrict
-/

#print Set.MapsTo.range_restrict /-
theorem MapsTo.range_restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) :
    range (h.restrict f s t) = coe ⁻¹' (f '' s) :=
  Set.range_subtype_map f h
#align set.maps_to.range_restrict Set.MapsTo.range_restrict
-/

#print Set.mapsTo_iff_exists_map_subtype /-
theorem mapsTo_iff_exists_map_subtype : MapsTo f s t ↔ ∃ g : s → t, ∀ x : s, f x = g x :=
  ⟨fun h => ⟨h.restrict f s t, fun _ => rfl⟩, fun ⟨g, hg⟩ x hx => by erw [hg ⟨x, hx⟩];
    apply Subtype.coe_prop⟩
#align set.maps_to_iff_exists_map_subtype Set.mapsTo_iff_exists_map_subtype
-/

#print Set.mapsTo' /-
theorem mapsTo' : MapsTo f s t ↔ f '' s ⊆ t :=
  image_subset_iff.symm
#align set.maps_to' Set.mapsTo'
-/

#print Set.mapsTo_prod_map_diagonal /-
theorem mapsTo_prod_map_diagonal : MapsTo (Prod.map f f) (diagonal α) (diagonal β) :=
  diagonal_subset_iff.2 fun x => rfl
#align set.maps_to_prod_map_diagonal Set.mapsTo_prod_map_diagonal
-/

#print Set.MapsTo.subset_preimage /-
theorem MapsTo.subset_preimage {f : α → β} {s : Set α} {t : Set β} (hf : MapsTo f s t) :
    s ⊆ f ⁻¹' t :=
  hf
#align set.maps_to.subset_preimage Set.MapsTo.subset_preimage
-/

#print Set.mapsTo_empty /-
theorem mapsTo_empty (f : α → β) (t : Set β) : MapsTo f ∅ t :=
  empty_subset _
#align set.maps_to_empty Set.mapsTo_empty
-/

#print Set.mapsTo_singleton /-
@[simp]
theorem mapsTo_singleton : MapsTo f {a} t ↔ f a ∈ t :=
  singleton_subset_iff
#align set.maps_to_singleton Set.mapsTo_singleton
-/

#print Set.MapsTo.image_subset /-
theorem MapsTo.image_subset (h : MapsTo f s t) : f '' s ⊆ t :=
  mapsTo'.1 h
#align set.maps_to.image_subset Set.MapsTo.image_subset
-/

#print Set.MapsTo.congr /-
theorem MapsTo.congr (h₁ : MapsTo f₁ s t) (h : EqOn f₁ f₂ s) : MapsTo f₂ s t := fun x hx =>
  h hx ▸ h₁ hx
#align set.maps_to.congr Set.MapsTo.congr
-/

#print Set.EqOn.comp_right /-
theorem EqOn.comp_right (hg : t.EqOn g₁ g₂) (hf : s.MapsTo f t) : s.EqOn (g₁ ∘ f) (g₂ ∘ f) :=
  fun a ha => hg <| hf ha
#align set.eq_on.comp_right Set.EqOn.comp_right
-/

#print Set.EqOn.mapsTo_iff /-
theorem EqOn.mapsTo_iff (H : EqOn f₁ f₂ s) : MapsTo f₁ s t ↔ MapsTo f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩
#align set.eq_on.maps_to_iff Set.EqOn.mapsTo_iff
-/

#print Set.MapsTo.comp /-
theorem MapsTo.comp (h₁ : MapsTo g t p) (h₂ : MapsTo f s t) : MapsTo (g ∘ f) s p := fun x h =>
  h₁ (h₂ h)
#align set.maps_to.comp Set.MapsTo.comp
-/

#print Set.mapsTo_id /-
theorem mapsTo_id (s : Set α) : MapsTo id s s := fun x => id
#align set.maps_to_id Set.mapsTo_id
-/

#print Set.MapsTo.iterate /-
theorem MapsTo.iterate {f : α → α} {s : Set α} (h : MapsTo f s s) : ∀ n, MapsTo (f^[n]) s s
  | 0 => fun _ => id
  | n + 1 => (maps_to.iterate n).comp h
#align set.maps_to.iterate Set.MapsTo.iterate
-/

#print Set.MapsTo.iterate_restrict /-
theorem MapsTo.iterate_restrict {f : α → α} {s : Set α} (h : MapsTo f s s) (n : ℕ) :
    h.restrict f s s^[n] = (h.iterate n).restrict _ _ _ :=
  by
  funext x
  rw [Subtype.ext_iff, maps_to.coe_restrict_apply]
  induction' n with n ihn generalizing x
  · rfl
  · simp [Nat.iterate, ihn]
#align set.maps_to.iterate_restrict Set.MapsTo.iterate_restrict
-/

#print Set.mapsTo_of_subsingleton' /-
theorem mapsTo_of_subsingleton' [Subsingleton β] (f : α → β) (h : s.Nonempty → t.Nonempty) :
    MapsTo f s t := fun a ha => Subsingleton.mem_iff_nonempty.2 <| h ⟨a, ha⟩
#align set.maps_to_of_subsingleton' Set.mapsTo_of_subsingleton'
-/

#print Set.mapsTo_of_subsingleton /-
theorem mapsTo_of_subsingleton [Subsingleton α] (f : α → α) (s : Set α) : MapsTo f s s :=
  mapsTo_of_subsingleton' _ id
#align set.maps_to_of_subsingleton Set.mapsTo_of_subsingleton
-/

#print Set.MapsTo.mono /-
theorem MapsTo.mono (hf : MapsTo f s₁ t₁) (hs : s₂ ⊆ s₁) (ht : t₁ ⊆ t₂) : MapsTo f s₂ t₂ :=
  fun x hx => ht (hf <| hs hx)
#align set.maps_to.mono Set.MapsTo.mono
-/

#print Set.MapsTo.mono_left /-
theorem MapsTo.mono_left (hf : MapsTo f s₁ t) (hs : s₂ ⊆ s₁) : MapsTo f s₂ t := fun x hx =>
  hf (hs hx)
#align set.maps_to.mono_left Set.MapsTo.mono_left
-/

#print Set.MapsTo.mono_right /-
theorem MapsTo.mono_right (hf : MapsTo f s t₁) (ht : t₁ ⊆ t₂) : MapsTo f s t₂ := fun x hx =>
  ht (hf hx)
#align set.maps_to.mono_right Set.MapsTo.mono_right
-/

#print Set.MapsTo.union_union /-
theorem MapsTo.union_union (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) :
    MapsTo f (s₁ ∪ s₂) (t₁ ∪ t₂) := fun x hx =>
  hx.elim (fun hx => Or.inl <| h₁ hx) fun hx => Or.inr <| h₂ hx
#align set.maps_to.union_union Set.MapsTo.union_union
-/

#print Set.MapsTo.union /-
theorem MapsTo.union (h₁ : MapsTo f s₁ t) (h₂ : MapsTo f s₂ t) : MapsTo f (s₁ ∪ s₂) t :=
  union_self t ▸ h₁.union_union h₂
#align set.maps_to.union Set.MapsTo.union
-/

#print Set.mapsTo_union /-
@[simp]
theorem mapsTo_union : MapsTo f (s₁ ∪ s₂) t ↔ MapsTo f s₁ t ∧ MapsTo f s₂ t :=
  ⟨fun h =>
    ⟨h.mono (subset_union_left s₁ s₂) (Subset.refl t),
      h.mono (subset_union_right s₁ s₂) (Subset.refl t)⟩,
    fun h => h.1.union h.2⟩
#align set.maps_to_union Set.mapsTo_union
-/

#print Set.MapsTo.inter /-
theorem MapsTo.inter (h₁ : MapsTo f s t₁) (h₂ : MapsTo f s t₂) : MapsTo f s (t₁ ∩ t₂) := fun x hx =>
  ⟨h₁ hx, h₂ hx⟩
#align set.maps_to.inter Set.MapsTo.inter
-/

#print Set.MapsTo.inter_inter /-
theorem MapsTo.inter_inter (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) :
    MapsTo f (s₁ ∩ s₂) (t₁ ∩ t₂) := fun x hx => ⟨h₁ hx.1, h₂ hx.2⟩
#align set.maps_to.inter_inter Set.MapsTo.inter_inter
-/

#print Set.mapsTo_inter /-
@[simp]
theorem mapsTo_inter : MapsTo f s (t₁ ∩ t₂) ↔ MapsTo f s t₁ ∧ MapsTo f s t₂ :=
  ⟨fun h =>
    ⟨h.mono (Subset.refl s) (inter_subset_left t₁ t₂),
      h.mono (Subset.refl s) (inter_subset_right t₁ t₂)⟩,
    fun h => h.1.inter h.2⟩
#align set.maps_to_inter Set.mapsTo_inter
-/

#print Set.mapsTo_univ /-
theorem mapsTo_univ (f : α → β) (s : Set α) : MapsTo f s univ := fun x h => trivial
#align set.maps_to_univ Set.mapsTo_univ
-/

#print Set.mapsTo_image /-
theorem mapsTo_image (f : α → β) (s : Set α) : MapsTo f s (f '' s) := by rw [maps_to']
#align set.maps_to_image Set.mapsTo_image
-/

#print Set.mapsTo_preimage /-
theorem mapsTo_preimage (f : α → β) (t : Set β) : MapsTo f (f ⁻¹' t) t :=
  Subset.refl _
#align set.maps_to_preimage Set.mapsTo_preimage
-/

#print Set.mapsTo_range /-
theorem mapsTo_range (f : α → β) (s : Set α) : MapsTo f s (range f) :=
  (mapsTo_image f s).mono (Subset.refl s) (image_subset_range _ _)
#align set.maps_to_range Set.mapsTo_range
-/

#print Set.mapsTo_image_iff /-
@[simp]
theorem mapsTo_image_iff (f : α → β) (g : γ → α) (s : Set γ) (t : Set β) :
    MapsTo f (g '' s) t ↔ MapsTo (f ∘ g) s t :=
  ⟨fun h c hc => h ⟨c, hc, rfl⟩, fun h d ⟨c, hc⟩ => hc.2 ▸ h hc.1⟩
#align set.maps_image_to Set.mapsTo_image_iff
-/

#print Set.MapsTo.comp_left /-
theorem MapsTo.comp_left (g : β → γ) (hf : MapsTo f s t) : MapsTo (g ∘ f) s (g '' t) := fun x hx =>
  ⟨f x, hf hx, rfl⟩
#align set.maps_to.comp_left Set.MapsTo.comp_left
-/

#print Set.MapsTo.comp_right /-
theorem MapsTo.comp_right {s : Set β} {t : Set γ} (hg : MapsTo g s t) (f : α → β) :
    MapsTo (g ∘ f) (f ⁻¹' s) t := fun x hx => hg hx
#align set.maps_to.comp_right Set.MapsTo.comp_right
-/

#print Set.maps_univ_to /-
@[simp]
theorem maps_univ_to (f : α → β) (s : Set β) : MapsTo f univ s ↔ ∀ a, f a ∈ s :=
  ⟨fun h a => h (mem_univ _), fun h x _ => h x⟩
#align set.maps_univ_to Set.maps_univ_to
-/

#print Set.maps_range_to /-
@[simp]
theorem maps_range_to (f : α → β) (g : γ → α) (s : Set β) :
    MapsTo f (range g) s ↔ MapsTo (f ∘ g) univ s := by rw [← image_univ, maps_image_to]
#align set.maps_range_to Set.maps_range_to
-/

#print Set.surjective_mapsTo_image_restrict /-
theorem surjective_mapsTo_image_restrict (f : α → β) (s : Set α) :
    Surjective ((mapsTo_image f s).restrict f s (f '' s)) := fun ⟨y, x, hs, hxy⟩ =>
  ⟨⟨x, hs⟩, Subtype.ext hxy⟩
#align set.surjective_maps_to_image_restrict Set.surjective_mapsTo_image_restrict
-/

#print Set.MapsTo.mem_iff /-
theorem MapsTo.mem_iff (h : MapsTo f s t) (hc : MapsTo f (sᶜ) (tᶜ)) {x} : f x ∈ t ↔ x ∈ s :=
  ⟨fun ht => by_contra fun hs => hc hs ht, fun hx => h hx⟩
#align set.maps_to.mem_iff Set.MapsTo.mem_iff
-/

/-! ### Restriction onto preimage -/


section

variable (t f)

#print Set.restrictPreimage /-
/-- The restriction of a function onto the preimage of a set. -/
@[simps]
def restrictPreimage : f ⁻¹' t → t :=
  (Set.mapsTo_preimage f t).restrict _ _ _
#align set.restrict_preimage Set.restrictPreimage
-/

#print Set.range_restrictPreimage /-
theorem range_restrictPreimage : range (t.restrictPreimage f) = coe ⁻¹' range f :=
  by
  delta Set.restrictPreimage
  rw [maps_to.range_restrict, Set.image_preimage_eq_inter_range, Set.preimage_inter,
    Subtype.coe_preimage_self, Set.univ_inter]
#align set.range_restrict_preimage Set.range_restrictPreimage
-/

variable {f} {U : ι → Set β}

#print Set.restrictPreimage_injective /-
theorem restrictPreimage_injective (hf : Injective f) : Injective (t.restrictPreimage f) :=
  fun x y e => Subtype.mk.injArrow e fun e => Subtype.coe_injective (hf e)
#align set.restrict_preimage_injective Set.restrictPreimage_injective
-/

#print Set.restrictPreimage_surjective /-
theorem restrictPreimage_surjective (hf : Surjective f) : Surjective (t.restrictPreimage f) :=
  fun x =>
  ⟨⟨_, show f (hf x).some ∈ t from (hf x).choose_spec.symm ▸ x.2⟩, Subtype.ext (hf x).choose_spec⟩
#align set.restrict_preimage_surjective Set.restrictPreimage_surjective
-/

#print Set.restrictPreimage_bijective /-
theorem restrictPreimage_bijective (hf : Bijective f) : Bijective (t.restrictPreimage f) :=
  ⟨t.restrictPreimage_injective hf.1, t.restrictPreimage_surjective hf.2⟩
#align set.restrict_preimage_bijective Set.restrictPreimage_bijective
-/

alias _root_.function.injective.restrict_preimage := Set.restrictPreimage_injective
#align function.injective.restrict_preimage Function.Injective.restrictPreimage

alias _root_.function.surjective.restrict_preimage := Set.restrictPreimage_surjective
#align function.surjective.restrict_preimage Function.Surjective.restrictPreimage

alias _root_.function.bijective.restrict_preimage := Set.restrictPreimage_bijective
#align function.bijective.restrict_preimage Function.Bijective.restrictPreimage

end

/-! ### Injectivity on a set -/


#print Set.InjOn /-
/-- `f` is injective on `a` if the restriction of `f` to `a` is injective. -/
def InjOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x₁ : α⦄, x₁ ∈ s → ∀ ⦃x₂ : α⦄, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂
#align set.inj_on Set.InjOn
-/

#print Set.Subsingleton.injOn /-
theorem Subsingleton.injOn (hs : s.Subsingleton) (f : α → β) : InjOn f s := fun x hx y hy h =>
  hs hx hy
#align set.subsingleton.inj_on Set.Subsingleton.injOn
-/

#print Set.injOn_empty /-
@[simp]
theorem injOn_empty (f : α → β) : InjOn f ∅ :=
  subsingleton_empty.InjOn f
#align set.inj_on_empty Set.injOn_empty
-/

#print Set.injOn_singleton /-
@[simp]
theorem injOn_singleton (f : α → β) (a : α) : InjOn f {a} :=
  subsingleton_singleton.InjOn f
#align set.inj_on_singleton Set.injOn_singleton
-/

#print Set.InjOn.eq_iff /-
theorem InjOn.eq_iff {x y} (h : InjOn f s) (hx : x ∈ s) (hy : y ∈ s) : f x = f y ↔ x = y :=
  ⟨h hx hy, fun h => h ▸ rfl⟩
#align set.inj_on.eq_iff Set.InjOn.eq_iff
-/

#print Set.InjOn.ne_iff /-
theorem InjOn.ne_iff {x y} (h : InjOn f s) (hx : x ∈ s) (hy : y ∈ s) : f x ≠ f y ↔ x ≠ y :=
  (h.eq_iff hx hy).Not
#align set.inj_on.ne_iff Set.InjOn.ne_iff
-/

alias ⟨_, inj_on.ne⟩ := inj_on.ne_iff
#align set.inj_on.ne Set.InjOn.ne

#print Set.InjOn.congr /-
theorem InjOn.congr (h₁ : InjOn f₁ s) (h : EqOn f₁ f₂ s) : InjOn f₂ s := fun x hx y hy =>
  h hx ▸ h hy ▸ h₁ hx hy
#align set.inj_on.congr Set.InjOn.congr
-/

#print Set.EqOn.injOn_iff /-
theorem EqOn.injOn_iff (H : EqOn f₁ f₂ s) : InjOn f₁ s ↔ InjOn f₂ s :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩
#align set.eq_on.inj_on_iff Set.EqOn.injOn_iff
-/

#print Set.InjOn.mono /-
theorem InjOn.mono (h : s₁ ⊆ s₂) (ht : InjOn f s₂) : InjOn f s₁ := fun x hx y hy H =>
  ht (h hx) (h hy) H
#align set.inj_on.mono Set.InjOn.mono
-/

#print Set.injOn_union /-
theorem injOn_union (h : Disjoint s₁ s₂) :
    InjOn f (s₁ ∪ s₂) ↔ InjOn f s₁ ∧ InjOn f s₂ ∧ ∀ x ∈ s₁, ∀ y ∈ s₂, f x ≠ f y :=
  by
  refine' ⟨fun H => ⟨H.mono <| subset_union_left _ _, H.mono <| subset_union_right _ _, _⟩, _⟩
  · intro x hx y hy hxy
    obtain rfl : x = y; exact H (Or.inl hx) (Or.inr hy) hxy
    exact h.le_bot ⟨hx, hy⟩
  · rintro ⟨h₁, h₂, h₁₂⟩
    rintro x (hx | hx) y (hy | hy) hxy
    exacts [h₁ hx hy hxy, (h₁₂ _ hx _ hy hxy).elim, (h₁₂ _ hy _ hx hxy.symm).elim, h₂ hx hy hxy]
#align set.inj_on_union Set.injOn_union
-/

#print Set.injOn_insert /-
theorem injOn_insert {f : α → β} {s : Set α} {a : α} (has : a ∉ s) :
    Set.InjOn f (insert a s) ↔ Set.InjOn f s ∧ f a ∉ f '' s :=
  by
  have : Disjoint s {a} := disjoint_iff_inf_le.mpr fun x ⟨hxs, (hxa : x = a)⟩ => has (hxa ▸ hxs)
  rw [← union_singleton, inj_on_union this]
  simp
#align set.inj_on_insert Set.injOn_insert
-/

#print Set.injective_iff_injOn_univ /-
theorem injective_iff_injOn_univ : Injective f ↔ InjOn f univ :=
  ⟨fun h x hx y hy hxy => h hxy, fun h _ _ heq => h trivial trivial HEq⟩
#align set.injective_iff_inj_on_univ Set.injective_iff_injOn_univ
-/

#print Set.injOn_of_injective /-
theorem injOn_of_injective (h : Injective f) (s : Set α) : InjOn f s := fun x hx y hy hxy => h hxy
#align set.inj_on_of_injective Set.injOn_of_injective
-/

alias _root_.function.injective.inj_on := inj_on_of_injective
#align function.injective.inj_on Function.Injective.injOn

#print Set.injOn_id /-
theorem injOn_id (s : Set α) : InjOn id s :=
  injective_id.InjOn _
#align set.inj_on_id Set.injOn_id
-/

#print Set.InjOn.comp /-
theorem InjOn.comp (hg : InjOn g t) (hf : InjOn f s) (h : MapsTo f s t) : InjOn (g ∘ f) s :=
  fun x hx y hy heq => hf hx hy <| hg (h hx) (h hy) HEq
#align set.inj_on.comp Set.InjOn.comp
-/

#print Set.InjOn.iterate /-
theorem InjOn.iterate {f : α → α} {s : Set α} (h : InjOn f s) (hf : MapsTo f s s) :
    ∀ n, InjOn (f^[n]) s
  | 0 => injOn_id _
  | n + 1 => (inj_on.iterate n).comp h hf
#align set.inj_on.iterate Set.InjOn.iterate
-/

#print Set.injOn_of_subsingleton /-
theorem injOn_of_subsingleton [Subsingleton α] (f : α → β) (s : Set α) : InjOn f s :=
  (injective_of_subsingleton _).InjOn _
#align set.inj_on_of_subsingleton Set.injOn_of_subsingleton
-/

#print Function.Injective.injOn_range /-
theorem Function.Injective.injOn_range (h : Injective (g ∘ f)) : InjOn g (range f) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ H; exact congr_arg f (h H)
#align function.injective.inj_on_range Function.Injective.injOn_range
-/

#print Set.injOn_iff_injective /-
theorem injOn_iff_injective : InjOn f s ↔ Injective (s.restrict f) :=
  ⟨fun H a b h => Subtype.eq <| H a.2 b.2 h, fun H a as b bs h =>
    congr_arg Subtype.val <| @H ⟨a, as⟩ ⟨b, bs⟩ h⟩
#align set.inj_on_iff_injective Set.injOn_iff_injective
-/

alias ⟨inj_on.injective, _⟩ := inj_on_iff_injective
#align set.inj_on.injective Set.InjOn.injective

#print Set.MapsTo.restrict_inj /-
theorem MapsTo.restrict_inj (h : MapsTo f s t) : Injective (h.restrict f s t) ↔ InjOn f s := by
  rw [h.restrict_eq_cod_restrict, injective_cod_restrict, inj_on_iff_injective]
#align set.maps_to.restrict_inj Set.MapsTo.restrict_inj
-/

#print Set.exists_injOn_iff_injective /-
theorem exists_injOn_iff_injective [Nonempty β] :
    (∃ f : α → β, InjOn f s) ↔ ∃ f : s → β, Injective f :=
  ⟨fun ⟨f, hf⟩ => ⟨_, hf.Injective⟩, fun ⟨f, hf⟩ => by lift f to α → β using trivial;
    exact ⟨f, inj_on_iff_injective.2 hf⟩⟩
#align set.exists_inj_on_iff_injective Set.exists_injOn_iff_injective
-/

#print Set.injOn_preimage /-
theorem injOn_preimage {B : Set (Set β)} (hB : B ⊆ 𝒫 range f) : InjOn (preimage f) B :=
  fun s hs t ht hst => (preimage_eq_preimage' (hB hs) (hB ht)).1 hst
#align set.inj_on_preimage Set.injOn_preimage
-/

#print Set.InjOn.mem_of_mem_image /-
theorem InjOn.mem_of_mem_image {x} (hf : InjOn f s) (hs : s₁ ⊆ s) (h : x ∈ s) (h₁ : f x ∈ f '' s₁) :
    x ∈ s₁ :=
  let ⟨x', h', Eq⟩ := h₁
  hf (hs h') h Eq ▸ h'
#align set.inj_on.mem_of_mem_image Set.InjOn.mem_of_mem_image
-/

#print Set.InjOn.mem_image_iff /-
theorem InjOn.mem_image_iff {x} (hf : InjOn f s) (hs : s₁ ⊆ s) (hx : x ∈ s) :
    f x ∈ f '' s₁ ↔ x ∈ s₁ :=
  ⟨hf.mem_of_mem_image hs hx, mem_image_of_mem f⟩
#align set.inj_on.mem_image_iff Set.InjOn.mem_image_iff
-/

#print Set.InjOn.preimage_image_inter /-
theorem InjOn.preimage_image_inter (hf : InjOn f s) (hs : s₁ ⊆ s) : f ⁻¹' (f '' s₁) ∩ s = s₁ :=
  ext fun x => ⟨fun ⟨h₁, h₂⟩ => hf.mem_of_mem_image hs h₂ h₁, fun h => ⟨mem_image_of_mem _ h, hs h⟩⟩
#align set.inj_on.preimage_image_inter Set.InjOn.preimage_image_inter
-/

#print Set.EqOn.cancel_left /-
theorem EqOn.cancel_left (h : s.EqOn (g ∘ f₁) (g ∘ f₂)) (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t)
    (hf₂ : s.MapsTo f₂ t) : s.EqOn f₁ f₂ := fun a ha => hg (hf₁ ha) (hf₂ ha) (h ha)
#align set.eq_on.cancel_left Set.EqOn.cancel_left
-/

#print Set.InjOn.cancel_left /-
theorem InjOn.cancel_left (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t) (hf₂ : s.MapsTo f₂ t) :
    s.EqOn (g ∘ f₁) (g ∘ f₂) ↔ s.EqOn f₁ f₂ :=
  ⟨fun h => h.cancel_left hg hf₁ hf₂, EqOn.comp_left⟩
#align set.inj_on.cancel_left Set.InjOn.cancel_left
-/

#print Set.InjOn.image_inter /-
theorem InjOn.image_inter {s t u : Set α} (hf : u.InjOn f) (hs : s ⊆ u) (ht : t ⊆ u) :
    f '' (s ∩ t) = f '' s ∩ f '' t :=
  by
  apply subset.antisymm (image_inter_subset _ _ _)
  rintro x ⟨⟨y, ys, hy⟩, ⟨z, zt, hz⟩⟩
  have : y = z := by
    apply hf (hs ys) (ht zt)
    rwa [← hz] at hy
  rw [← this] at zt
  exact ⟨y, ⟨ys, zt⟩, hy⟩
#align set.inj_on.image_inter Set.InjOn.image_inter
-/

#print Disjoint.image /-
theorem Disjoint.image {s t u : Set α} {f : α → β} (h : Disjoint s t) (hf : InjOn f u) (hs : s ⊆ u)
    (ht : t ⊆ u) : Disjoint (f '' s) (f '' t) :=
  by
  rw [disjoint_iff_inter_eq_empty] at h ⊢
  rw [← hf.image_inter hs ht, h, image_empty]
#align disjoint.image Disjoint.image
-/

/-! ### Surjectivity on a set -/


#print Set.SurjOn /-
/-- `f` is surjective from `a` to `b` if `b` is contained in the image of `a`. -/
def SurjOn (f : α → β) (s : Set α) (t : Set β) : Prop :=
  t ⊆ f '' s
#align set.surj_on Set.SurjOn
-/

#print Set.SurjOn.subset_range /-
theorem SurjOn.subset_range (h : SurjOn f s t) : t ⊆ range f :=
  Subset.trans h <| image_subset_range f s
#align set.surj_on.subset_range Set.SurjOn.subset_range
-/

#print Set.surjOn_iff_exists_map_subtype /-
theorem surjOn_iff_exists_map_subtype :
    SurjOn f s t ↔ ∃ (t' : Set β) (g : s → t'), t ⊆ t' ∧ Surjective g ∧ ∀ x : s, f x = g x :=
  ⟨fun h =>
    ⟨_, (mapsTo_image f s).restrict f s _, h, surjective_mapsTo_image_restrict _ _, fun _ => rfl⟩,
    fun ⟨t', g, htt', hg, hfg⟩ y hy =>
    let ⟨x, hx⟩ := hg ⟨y, htt' hy⟩
    ⟨x, x.2, by rw [hfg, hx, Subtype.coe_mk]⟩⟩
#align set.surj_on_iff_exists_map_subtype Set.surjOn_iff_exists_map_subtype
-/

#print Set.surjOn_empty /-
theorem surjOn_empty (f : α → β) (s : Set α) : SurjOn f s ∅ :=
  empty_subset _
#align set.surj_on_empty Set.surjOn_empty
-/

#print Set.surjOn_singleton /-
@[simp]
theorem surjOn_singleton : SurjOn f s {b} ↔ b ∈ f '' s :=
  singleton_subset_iff
#align set.surj_on_singleton Set.surjOn_singleton
-/

#print Set.surjOn_image /-
theorem surjOn_image (f : α → β) (s : Set α) : SurjOn f s (f '' s) :=
  Subset.rfl
#align set.surj_on_image Set.surjOn_image
-/

#print Set.SurjOn.comap_nonempty /-
theorem SurjOn.comap_nonempty (h : SurjOn f s t) (ht : t.Nonempty) : s.Nonempty :=
  (ht.mono h).of_image
#align set.surj_on.comap_nonempty Set.SurjOn.comap_nonempty
-/

#print Set.SurjOn.congr /-
theorem SurjOn.congr (h : SurjOn f₁ s t) (H : EqOn f₁ f₂ s) : SurjOn f₂ s t := by
  rwa [surj_on, ← H.image_eq]
#align set.surj_on.congr Set.SurjOn.congr
-/

#print Set.EqOn.surjOn_iff /-
theorem EqOn.surjOn_iff (h : EqOn f₁ f₂ s) : SurjOn f₁ s t ↔ SurjOn f₂ s t :=
  ⟨fun H => H.congr h, fun H => H.congr h.symm⟩
#align set.eq_on.surj_on_iff Set.EqOn.surjOn_iff
-/

#print Set.SurjOn.mono /-
theorem SurjOn.mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (hf : SurjOn f s₁ t₂) : SurjOn f s₂ t₁ :=
  Subset.trans ht <| Subset.trans hf <| image_subset _ hs
#align set.surj_on.mono Set.SurjOn.mono
-/

#print Set.SurjOn.union /-
theorem SurjOn.union (h₁ : SurjOn f s t₁) (h₂ : SurjOn f s t₂) : SurjOn f s (t₁ ∪ t₂) := fun x hx =>
  hx.elim (fun hx => h₁ hx) fun hx => h₂ hx
#align set.surj_on.union Set.SurjOn.union
-/

#print Set.SurjOn.union_union /-
theorem SurjOn.union_union (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) :
    SurjOn f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  (h₁.mono (subset_union_left _ _) (Subset.refl _)).union
    (h₂.mono (subset_union_right _ _) (Subset.refl _))
#align set.surj_on.union_union Set.SurjOn.union_union
-/

#print Set.SurjOn.inter_inter /-
theorem SurjOn.inter_inter (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    SurjOn f (s₁ ∩ s₂) (t₁ ∩ t₂) := by
  intro y hy
  rcases h₁ hy.1 with ⟨x₁, hx₁, rfl⟩
  rcases h₂ hy.2 with ⟨x₂, hx₂, heq⟩
  obtain rfl : x₁ = x₂ := h (Or.inl hx₁) (Or.inr hx₂) HEq.symm
  exact mem_image_of_mem f ⟨hx₁, hx₂⟩
#align set.surj_on.inter_inter Set.SurjOn.inter_inter
-/

#print Set.SurjOn.inter /-
theorem SurjOn.inter (h₁ : SurjOn f s₁ t) (h₂ : SurjOn f s₂ t) (h : InjOn f (s₁ ∪ s₂)) :
    SurjOn f (s₁ ∩ s₂) t :=
  inter_self t ▸ h₁.inter_inter h₂ h
#align set.surj_on.inter Set.SurjOn.inter
-/

#print Set.surjOn_id /-
theorem surjOn_id (s : Set α) : SurjOn id s s := by simp [surj_on]
#align set.surj_on_id Set.surjOn_id
-/

#print Set.SurjOn.comp /-
theorem SurjOn.comp (hg : SurjOn g t p) (hf : SurjOn f s t) : SurjOn (g ∘ f) s p :=
  Subset.trans hg <| Subset.trans (image_subset g hf) <| image_comp g f s ▸ Subset.refl _
#align set.surj_on.comp Set.SurjOn.comp
-/

#print Set.SurjOn.iterate /-
theorem SurjOn.iterate {f : α → α} {s : Set α} (h : SurjOn f s s) : ∀ n, SurjOn (f^[n]) s s
  | 0 => surjOn_id _
  | n + 1 => (surj_on.iterate n).comp h
#align set.surj_on.iterate Set.SurjOn.iterate
-/

#print Set.SurjOn.comp_left /-
theorem SurjOn.comp_left (hf : SurjOn f s t) (g : β → γ) : SurjOn (g ∘ f) s (g '' t) := by
  rw [surj_on, image_comp g f]; exact image_subset _ hf
#align set.surj_on.comp_left Set.SurjOn.comp_left
-/

#print Set.SurjOn.comp_right /-
theorem SurjOn.comp_right {s : Set β} {t : Set γ} (hf : Surjective f) (hg : SurjOn g s t) :
    SurjOn (g ∘ f) (f ⁻¹' s) t := by rwa [surj_on, image_comp g f, image_preimage_eq _ hf]
#align set.surj_on.comp_right Set.SurjOn.comp_right
-/

#print Set.surjOn_of_subsingleton' /-
theorem surjOn_of_subsingleton' [Subsingleton β] (f : α → β) (h : t.Nonempty → s.Nonempty) :
    SurjOn f s t := fun a ha => Subsingleton.mem_iff_nonempty.2 <| (h ⟨a, ha⟩).image _
#align set.surj_on_of_subsingleton' Set.surjOn_of_subsingleton'
-/

#print Set.surjOn_of_subsingleton /-
theorem surjOn_of_subsingleton [Subsingleton α] (f : α → α) (s : Set α) : SurjOn f s s :=
  surjOn_of_subsingleton' _ id
#align set.surj_on_of_subsingleton Set.surjOn_of_subsingleton
-/

#print Set.surjective_iff_surjOn_univ /-
theorem surjective_iff_surjOn_univ : Surjective f ↔ SurjOn f univ univ := by
  simp [surjective, surj_on, subset_def]
#align set.surjective_iff_surj_on_univ Set.surjective_iff_surjOn_univ
-/

#print Set.surjOn_iff_surjective /-
theorem surjOn_iff_surjective : SurjOn f s univ ↔ Surjective (s.restrict f) :=
  ⟨fun H b =>
    let ⟨a, as, e⟩ := @H b trivial
    ⟨⟨a, as⟩, e⟩,
    fun H b _ =>
    let ⟨⟨a, as⟩, e⟩ := H b
    ⟨a, as, e⟩⟩
#align set.surj_on_iff_surjective Set.surjOn_iff_surjective
-/

#print Set.SurjOn.image_eq_of_mapsTo /-
theorem SurjOn.image_eq_of_mapsTo (h₁ : SurjOn f s t) (h₂ : MapsTo f s t) : f '' s = t :=
  eq_of_subset_of_subset h₂.image_subset h₁
#align set.surj_on.image_eq_of_maps_to Set.SurjOn.image_eq_of_mapsTo
-/

#print Set.image_eq_iff_surjOn_mapsTo /-
theorem image_eq_iff_surjOn_mapsTo : f '' s = t ↔ s.SurjOn f t ∧ s.MapsTo f t :=
  by
  refine' ⟨_, fun h => h.1.image_eq_of_mapsTo h.2⟩
  rintro rfl
  exact ⟨s.surj_on_image f, s.maps_to_image f⟩
#align set.image_eq_iff_surj_on_maps_to Set.image_eq_iff_surjOn_mapsTo
-/

#print Set.SurjOn.mapsTo_compl /-
theorem SurjOn.mapsTo_compl (h : SurjOn f s t) (h' : Injective f) : MapsTo f (sᶜ) (tᶜ) :=
  fun x hs ht =>
  let ⟨x', hx', HEq⟩ := h ht
  hs <| h' HEq ▸ hx'
#align set.surj_on.maps_to_compl Set.SurjOn.mapsTo_compl
-/

#print Set.MapsTo.surjOn_compl /-
theorem MapsTo.surjOn_compl (h : MapsTo f s t) (h' : Surjective f) : SurjOn f (sᶜ) (tᶜ) :=
  h'.forall.2 fun x ht => mem_image_of_mem _ fun hs => ht (h hs)
#align set.maps_to.surj_on_compl Set.MapsTo.surjOn_compl
-/

#print Set.EqOn.cancel_right /-
theorem EqOn.cancel_right (hf : s.EqOn (g₁ ∘ f) (g₂ ∘ f)) (hf' : s.SurjOn f t) : t.EqOn g₁ g₂ :=
  by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hf' hb
  exact hf ha
#align set.eq_on.cancel_right Set.EqOn.cancel_right
-/

#print Set.SurjOn.cancel_right /-
theorem SurjOn.cancel_right (hf : s.SurjOn f t) (hf' : s.MapsTo f t) :
    s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ t.EqOn g₁ g₂ :=
  ⟨fun h => h.cancel_right hf, fun h => h.compRight hf'⟩
#align set.surj_on.cancel_right Set.SurjOn.cancel_right
-/

#print Set.eqOn_comp_right_iff /-
theorem eqOn_comp_right_iff : s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ (f '' s).EqOn g₁ g₂ :=
  (s.surjOn_image f).cancel_right <| s.mapsTo_image f
#align set.eq_on_comp_right_iff Set.eqOn_comp_right_iff
-/

/-! ### Bijectivity -/


#print Set.BijOn /-
/-- `f` is bijective from `s` to `t` if `f` is injective on `s` and `f '' s = t`. -/
def BijOn (f : α → β) (s : Set α) (t : Set β) : Prop :=
  MapsTo f s t ∧ InjOn f s ∧ SurjOn f s t
#align set.bij_on Set.BijOn
-/

#print Set.BijOn.mapsTo /-
theorem BijOn.mapsTo (h : BijOn f s t) : MapsTo f s t :=
  h.left
#align set.bij_on.maps_to Set.BijOn.mapsTo
-/

#print Set.BijOn.injOn /-
theorem BijOn.injOn (h : BijOn f s t) : InjOn f s :=
  h.right.left
#align set.bij_on.inj_on Set.BijOn.injOn
-/

#print Set.BijOn.surjOn /-
theorem BijOn.surjOn (h : BijOn f s t) : SurjOn f s t :=
  h.right.right
#align set.bij_on.surj_on Set.BijOn.surjOn
-/

#print Set.BijOn.mk /-
theorem BijOn.mk (h₁ : MapsTo f s t) (h₂ : InjOn f s) (h₃ : SurjOn f s t) : BijOn f s t :=
  ⟨h₁, h₂, h₃⟩
#align set.bij_on.mk Set.BijOn.mk
-/

#print Set.bijOn_empty /-
@[simp]
theorem bijOn_empty (f : α → β) : BijOn f ∅ ∅ :=
  ⟨mapsTo_empty f ∅, injOn_empty f, surjOn_empty f ∅⟩
#align set.bij_on_empty Set.bijOn_empty
-/

#print Set.bijOn_singleton /-
@[simp]
theorem bijOn_singleton : BijOn f {a} {b} ↔ f a = b := by simp [bij_on, eq_comm]
#align set.bij_on_singleton Set.bijOn_singleton
-/

#print Set.BijOn.inter_mapsTo /-
theorem BijOn.inter_mapsTo (h₁ : BijOn f s₁ t₁) (h₂ : MapsTo f s₂ t₂) (h₃ : s₁ ∩ f ⁻¹' t₂ ⊆ s₂) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  ⟨h₁.MapsTo.inter_inter h₂, h₁.InjOn.mono <| inter_subset_left _ _, fun y hy =>
    let ⟨x, hx, hxy⟩ := h₁.SurjOn hy.1
    ⟨x, ⟨hx, h₃ ⟨hx, hxy.symm.recOn hy.2⟩⟩, hxy⟩⟩
#align set.bij_on.inter_maps_to Set.BijOn.inter_mapsTo
-/

#print Set.MapsTo.inter_bijOn /-
theorem MapsTo.inter_bijOn (h₁ : MapsTo f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h₃ : s₂ ∩ f ⁻¹' t₁ ⊆ s₁) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  inter_comm s₂ s₁ ▸ inter_comm t₂ t₁ ▸ h₂.inter_mapsTo h₁ h₃
#align set.maps_to.inter_bij_on Set.MapsTo.inter_bijOn
-/

#print Set.BijOn.inter /-
theorem BijOn.inter (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  ⟨h₁.MapsTo.inter_inter h₂.MapsTo, h₁.InjOn.mono <| inter_subset_left _ _,
    h₁.SurjOn.inter_inter h₂.SurjOn h⟩
#align set.bij_on.inter Set.BijOn.inter
-/

#print Set.BijOn.union /-
theorem BijOn.union (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    BijOn f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  ⟨h₁.MapsTo.union_union h₂.MapsTo, h, h₁.SurjOn.union_union h₂.SurjOn⟩
#align set.bij_on.union Set.BijOn.union
-/

#print Set.BijOn.subset_range /-
theorem BijOn.subset_range (h : BijOn f s t) : t ⊆ range f :=
  h.SurjOn.subset_range
#align set.bij_on.subset_range Set.BijOn.subset_range
-/

#print Set.InjOn.bijOn_image /-
theorem InjOn.bijOn_image (h : InjOn f s) : BijOn f s (f '' s) :=
  BijOn.mk (mapsTo_image f s) h (Subset.refl _)
#align set.inj_on.bij_on_image Set.InjOn.bijOn_image
-/

#print Set.BijOn.congr /-
theorem BijOn.congr (h₁ : BijOn f₁ s t) (h : EqOn f₁ f₂ s) : BijOn f₂ s t :=
  BijOn.mk (h₁.MapsTo.congr h) (h₁.InjOn.congr h) (h₁.SurjOn.congr h)
#align set.bij_on.congr Set.BijOn.congr
-/

#print Set.EqOn.bijOn_iff /-
theorem EqOn.bijOn_iff (H : EqOn f₁ f₂ s) : BijOn f₁ s t ↔ BijOn f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩
#align set.eq_on.bij_on_iff Set.EqOn.bijOn_iff
-/

#print Set.BijOn.image_eq /-
theorem BijOn.image_eq (h : BijOn f s t) : f '' s = t :=
  h.SurjOn.image_eq_of_mapsTo h.MapsTo
#align set.bij_on.image_eq Set.BijOn.image_eq
-/

#print Set.bijOn_id /-
theorem bijOn_id (s : Set α) : BijOn id s s :=
  ⟨s.mapsTo_id, s.injOn_id, s.surjOn_id⟩
#align set.bij_on_id Set.bijOn_id
-/

#print Set.BijOn.comp /-
theorem BijOn.comp (hg : BijOn g t p) (hf : BijOn f s t) : BijOn (g ∘ f) s p :=
  BijOn.mk (hg.MapsTo.comp hf.MapsTo) (hg.InjOn.comp hf.InjOn hf.MapsTo) (hg.SurjOn.comp hf.SurjOn)
#align set.bij_on.comp Set.BijOn.comp
-/

#print Set.BijOn.iterate /-
theorem BijOn.iterate {f : α → α} {s : Set α} (h : BijOn f s s) : ∀ n, BijOn (f^[n]) s s
  | 0 => s.bijOn_id
  | n + 1 => (bij_on.iterate n).comp h
#align set.bij_on.iterate Set.BijOn.iterate
-/

#print Set.bijOn_of_subsingleton' /-
theorem bijOn_of_subsingleton' [Subsingleton α] [Subsingleton β] (f : α → β)
    (h : s.Nonempty ↔ t.Nonempty) : BijOn f s t :=
  ⟨mapsTo_of_subsingleton' _ h.1, injOn_of_subsingleton _ _, surjOn_of_subsingleton' _ h.2⟩
#align set.bij_on_of_subsingleton' Set.bijOn_of_subsingleton'
-/

#print Set.bijOn_of_subsingleton /-
theorem bijOn_of_subsingleton [Subsingleton α] (f : α → α) (s : Set α) : BijOn f s s :=
  bijOn_of_subsingleton' _ Iff.rfl
#align set.bij_on_of_subsingleton Set.bijOn_of_subsingleton
-/

#print Set.BijOn.bijective /-
theorem BijOn.bijective (h : BijOn f s t) : Bijective (h.MapsTo.restrict f s t) :=
  ⟨fun x y h' => Subtype.ext <| h.InjOn x.2 y.2 <| Subtype.ext_iff.1 h', fun ⟨y, hy⟩ =>
    let ⟨x, hx, hxy⟩ := h.SurjOn hy
    ⟨⟨x, hx⟩, Subtype.eq hxy⟩⟩
#align set.bij_on.bijective Set.BijOn.bijective
-/

#print Set.bijective_iff_bijOn_univ /-
theorem bijective_iff_bijOn_univ : Bijective f ↔ BijOn f univ univ :=
  Iff.intro
    (fun h =>
      let ⟨inj, surj⟩ := h
      ⟨mapsTo_univ f _, inj.InjOn _, Iff.mp surjective_iff_surjOn_univ surj⟩)
    fun h =>
    let ⟨map, inj, surj⟩ := h
    ⟨Iff.mpr injective_iff_injOn_univ inj, Iff.mpr surjective_iff_surjOn_univ surj⟩
#align set.bijective_iff_bij_on_univ Set.bijective_iff_bijOn_univ
-/

alias ⟨_root_.function.bijective.bij_on_univ, _⟩ := bijective_iff_bij_on_univ
#align function.bijective.bij_on_univ Function.Bijective.bijOn_univ

#print Set.BijOn.compl /-
theorem BijOn.compl (hst : BijOn f s t) (hf : Bijective f) : BijOn f (sᶜ) (tᶜ) :=
  ⟨hst.SurjOn.mapsTo_compl hf.1, hf.1.InjOn _, hst.MapsTo.surjOn_compl hf.2⟩
#align set.bij_on.compl Set.BijOn.compl
-/

/-! ### left inverse -/


#print Set.LeftInvOn /-
/-- `g` is a left inverse to `f` on `a` means that `g (f x) = x` for all `x ∈ a`. -/
def LeftInvOn (f' : β → α) (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f' (f x) = x
#align set.left_inv_on Set.LeftInvOn
-/

@[simp]
theorem leftInvOn_empty (f' : β → α) (f : α → β) : LeftInvOn f' f ∅ :=
  empty_subset _
#align set.left_inv_on_empty Set.leftInvOn_empty

@[simp]
theorem leftInvOn_singleton : LeftInvOn f' f {a} ↔ f' (f a) = a :=
  singleton_subset_iff
#align set.left_inv_on_singleton Set.leftInvOn_singleton

#print Set.LeftInvOn.eqOn /-
theorem LeftInvOn.eqOn (h : LeftInvOn f' f s) : EqOn (f' ∘ f) id s :=
  h
#align set.left_inv_on.eq_on Set.LeftInvOn.eqOn
-/

#print Set.LeftInvOn.eq /-
theorem LeftInvOn.eq (h : LeftInvOn f' f s) {x} (hx : x ∈ s) : f' (f x) = x :=
  h hx
#align set.left_inv_on.eq Set.LeftInvOn.eq
-/

#print Set.LeftInvOn.congr_left /-
theorem LeftInvOn.congr_left (h₁ : LeftInvOn f₁' f s) {t : Set β} (h₁' : MapsTo f s t)
    (heq : EqOn f₁' f₂' t) : LeftInvOn f₂' f s := fun x hx => HEq (h₁' hx) ▸ h₁ hx
#align set.left_inv_on.congr_left Set.LeftInvOn.congr_left
-/

#print Set.LeftInvOn.congr_right /-
theorem LeftInvOn.congr_right (h₁ : LeftInvOn f₁' f₁ s) (heq : EqOn f₁ f₂ s) : LeftInvOn f₁' f₂ s :=
  fun x hx => HEq hx ▸ h₁ hx
#align set.left_inv_on.congr_right Set.LeftInvOn.congr_right
-/

#print Set.LeftInvOn.injOn /-
theorem LeftInvOn.injOn (h : LeftInvOn f₁' f s) : InjOn f s := fun x₁ h₁ x₂ h₂ heq =>
  calc
    x₁ = f₁' (f x₁) := Eq.symm <| h h₁
    _ = f₁' (f x₂) := (congr_arg f₁' HEq)
    _ = x₂ := h h₂
#align set.left_inv_on.inj_on Set.LeftInvOn.injOn
-/

#print Set.LeftInvOn.surjOn /-
theorem LeftInvOn.surjOn (h : LeftInvOn f' f s) (hf : MapsTo f s t) : SurjOn f' t s := fun x hx =>
  ⟨f x, hf hx, h hx⟩
#align set.left_inv_on.surj_on Set.LeftInvOn.surjOn
-/

#print Set.LeftInvOn.mapsTo /-
theorem LeftInvOn.mapsTo (h : LeftInvOn f' f s) (hf : SurjOn f s t) : MapsTo f' t s := fun y hy =>
  by
  let ⟨x, hs, hx⟩ := hf hy
  rwa [← hx, h hs]
#align set.left_inv_on.maps_to Set.LeftInvOn.mapsTo
-/

#print Set.leftInvOn_id /-
theorem leftInvOn_id (s : Set α) : LeftInvOn id id s := fun a _ => rfl
#align set.left_inv_on_id Set.leftInvOn_id
-/

#print Set.LeftInvOn.comp /-
theorem LeftInvOn.comp (hf' : LeftInvOn f' f s) (hg' : LeftInvOn g' g t) (hf : MapsTo f s t) :
    LeftInvOn (f' ∘ g') (g ∘ f) s := fun x h =>
  calc
    (f' ∘ g') ((g ∘ f) x) = f' (f x) := congr_arg f' (hg' (hf h))
    _ = x := hf' h
#align set.left_inv_on.comp Set.LeftInvOn.comp
-/

#print Set.LeftInvOn.mono /-
theorem LeftInvOn.mono (hf : LeftInvOn f' f s) (ht : s₁ ⊆ s) : LeftInvOn f' f s₁ := fun x hx =>
  hf (ht hx)
#align set.left_inv_on.mono Set.LeftInvOn.mono
-/

#print Set.LeftInvOn.image_inter' /-
theorem LeftInvOn.image_inter' (hf : LeftInvOn f' f s) : f '' (s₁ ∩ s) = f' ⁻¹' s₁ ∩ f '' s :=
  by
  apply subset.antisymm
  · rintro _ ⟨x, ⟨h₁, h⟩, rfl⟩; exact ⟨by rwa [mem_preimage, hf h], mem_image_of_mem _ h⟩
  · rintro _ ⟨h₁, ⟨x, h, rfl⟩⟩; exact mem_image_of_mem _ ⟨by rwa [← hf h], h⟩
#align set.left_inv_on.image_inter' Set.LeftInvOn.image_inter'
-/

#print Set.LeftInvOn.image_inter /-
theorem LeftInvOn.image_inter (hf : LeftInvOn f' f s) : f '' (s₁ ∩ s) = f' ⁻¹' (s₁ ∩ s) ∩ f '' s :=
  by
  rw [hf.image_inter']
  refine' subset.antisymm _ (inter_subset_inter_left _ (preimage_mono <| inter_subset_left _ _))
  rintro _ ⟨h₁, x, hx, rfl⟩; exact ⟨⟨h₁, by rwa [hf hx]⟩, mem_image_of_mem _ hx⟩
#align set.left_inv_on.image_inter Set.LeftInvOn.image_inter
-/

#print Set.LeftInvOn.image_image /-
theorem LeftInvOn.image_image (hf : LeftInvOn f' f s) : f' '' (f '' s) = s := by
  rw [image_image, image_congr hf, image_id']
#align set.left_inv_on.image_image Set.LeftInvOn.image_image
-/

#print Set.LeftInvOn.image_image' /-
theorem LeftInvOn.image_image' (hf : LeftInvOn f' f s) (hs : s₁ ⊆ s) : f' '' (f '' s₁) = s₁ :=
  (hf.mono hs).image_image
#align set.left_inv_on.image_image' Set.LeftInvOn.image_image'
-/

/-! ### Right inverse -/


#print Set.RightInvOn /-
/-- `g` is a right inverse to `f` on `b` if `f (g x) = x` for all `x ∈ b`. -/
@[reducible]
def RightInvOn (f' : β → α) (f : α → β) (t : Set β) : Prop :=
  LeftInvOn f f' t
#align set.right_inv_on Set.RightInvOn
-/

@[simp]
theorem rightInvOn_empty (f' : β → α) (f : α → β) : RightInvOn f' f ∅ :=
  empty_subset _
#align set.right_inv_on_empty Set.rightInvOn_empty

@[simp]
theorem rightInvOn_singleton : RightInvOn f' f {b} ↔ f (f' b) = b :=
  singleton_subset_iff
#align set.right_inv_on_singleton Set.rightInvOn_singleton

#print Set.RightInvOn.eqOn /-
theorem RightInvOn.eqOn (h : RightInvOn f' f t) : EqOn (f ∘ f') id t :=
  h
#align set.right_inv_on.eq_on Set.RightInvOn.eqOn
-/

#print Set.RightInvOn.eq /-
theorem RightInvOn.eq (h : RightInvOn f' f t) {y} (hy : y ∈ t) : f (f' y) = y :=
  h hy
#align set.right_inv_on.eq Set.RightInvOn.eq
-/

#print Set.LeftInvOn.rightInvOn_image /-
theorem LeftInvOn.rightInvOn_image (h : LeftInvOn f' f s) : RightInvOn f' f (f '' s) :=
  fun y ⟨x, hx, Eq⟩ => Eq ▸ congr_arg f <| h.Eq hx
#align set.left_inv_on.right_inv_on_image Set.LeftInvOn.rightInvOn_image
-/

#print Set.RightInvOn.congr_left /-
theorem RightInvOn.congr_left (h₁ : RightInvOn f₁' f t) (heq : EqOn f₁' f₂' t) :
    RightInvOn f₂' f t :=
  h₁.congr_right HEq
#align set.right_inv_on.congr_left Set.RightInvOn.congr_left
-/

#print Set.RightInvOn.congr_right /-
theorem RightInvOn.congr_right (h₁ : RightInvOn f' f₁ t) (hg : MapsTo f' t s) (heq : EqOn f₁ f₂ s) :
    RightInvOn f' f₂ t :=
  LeftInvOn.congr_left h₁ hg HEq
#align set.right_inv_on.congr_right Set.RightInvOn.congr_right
-/

#print Set.RightInvOn.surjOn /-
theorem RightInvOn.surjOn (hf : RightInvOn f' f t) (hf' : MapsTo f' t s) : SurjOn f s t :=
  hf.SurjOn hf'
#align set.right_inv_on.surj_on Set.RightInvOn.surjOn
-/

#print Set.RightInvOn.mapsTo /-
theorem RightInvOn.mapsTo (h : RightInvOn f' f t) (hf : SurjOn f' t s) : MapsTo f s t :=
  h.MapsTo hf
#align set.right_inv_on.maps_to Set.RightInvOn.mapsTo
-/

#print Set.rightInvOn_id /-
theorem rightInvOn_id (s : Set α) : RightInvOn id id s := fun a _ => rfl
#align set.right_inv_on_id Set.rightInvOn_id
-/

#print Set.RightInvOn.comp /-
theorem RightInvOn.comp (hf : RightInvOn f' f t) (hg : RightInvOn g' g p) (g'pt : MapsTo g' p t) :
    RightInvOn (f' ∘ g') (g ∘ f) p :=
  hg.comp hf g'pt
#align set.right_inv_on.comp Set.RightInvOn.comp
-/

#print Set.RightInvOn.mono /-
theorem RightInvOn.mono (hf : RightInvOn f' f t) (ht : t₁ ⊆ t) : RightInvOn f' f t₁ :=
  hf.mono ht
#align set.right_inv_on.mono Set.RightInvOn.mono
-/

#print Set.InjOn.rightInvOn_of_leftInvOn /-
theorem InjOn.rightInvOn_of_leftInvOn (hf : InjOn f s) (hf' : LeftInvOn f f' t) (h₁ : MapsTo f s t)
    (h₂ : MapsTo f' t s) : RightInvOn f f' s := fun x h => hf (h₂ <| h₁ h) h (hf' (h₁ h))
#align set.inj_on.right_inv_on_of_left_inv_on Set.InjOn.rightInvOn_of_leftInvOn
-/

#print Set.eqOn_of_leftInvOn_of_rightInvOn /-
theorem eqOn_of_leftInvOn_of_rightInvOn (h₁ : LeftInvOn f₁' f s) (h₂ : RightInvOn f₂' f t)
    (h : MapsTo f₂' t s) : EqOn f₁' f₂' t := fun y hy =>
  calc
    f₁' y = (f₁' ∘ f ∘ f₂') y := congr_arg f₁' (h₂ hy).symm
    _ = f₂' y := h₁ (h hy)
#align set.eq_on_of_left_inv_on_of_right_inv_on Set.eqOn_of_leftInvOn_of_rightInvOn
-/

#print Set.SurjOn.leftInvOn_of_rightInvOn /-
theorem SurjOn.leftInvOn_of_rightInvOn (hf : SurjOn f s t) (hf' : RightInvOn f f' s) :
    LeftInvOn f f' t := fun y hy => by
  let ⟨x, hx, HEq⟩ := hf hy
  rw [← HEq, hf' hx]
#align set.surj_on.left_inv_on_of_right_inv_on Set.SurjOn.leftInvOn_of_rightInvOn
-/

/-! ### Two-side inverses -/


#print Set.InvOn /-
/-- `g` is an inverse to `f` viewed as a map from `a` to `b` -/
def InvOn (g : β → α) (f : α → β) (s : Set α) (t : Set β) : Prop :=
  LeftInvOn g f s ∧ RightInvOn g f t
#align set.inv_on Set.InvOn
-/

@[simp]
theorem invOn_empty (f' : β → α) (f : α → β) : InvOn f' f ∅ ∅ := by simp [inv_on]
#align set.inv_on_empty Set.invOn_empty

@[simp]
theorem invOn_singleton : InvOn f' f {a} {b} ↔ f' (f a) = a ∧ f (f' b) = b := by simp [inv_on]
#align set.inv_on_singleton Set.invOn_singleton

#print Set.InvOn.symm /-
theorem InvOn.symm (h : InvOn f' f s t) : InvOn f f' t s :=
  ⟨h.right, h.left⟩
#align set.inv_on.symm Set.InvOn.symm
-/

#print Set.invOn_id /-
theorem invOn_id (s : Set α) : InvOn id id s s :=
  ⟨s.leftInvOn_id, s.rightInvOn_id⟩
#align set.inv_on_id Set.invOn_id
-/

#print Set.InvOn.comp /-
theorem InvOn.comp (hf : InvOn f' f s t) (hg : InvOn g' g t p) (fst : MapsTo f s t)
    (g'pt : MapsTo g' p t) : InvOn (f' ∘ g') (g ∘ f) s p :=
  ⟨hf.1.comp hg.1 fst, hf.2.comp hg.2 g'pt⟩
#align set.inv_on.comp Set.InvOn.comp
-/

#print Set.InvOn.mono /-
theorem InvOn.mono (h : InvOn f' f s t) (hs : s₁ ⊆ s) (ht : t₁ ⊆ t) : InvOn f' f s₁ t₁ :=
  ⟨h.1.mono hs, h.2.mono ht⟩
#align set.inv_on.mono Set.InvOn.mono
-/

#print Set.InvOn.bijOn /-
/-- If functions `f'` and `f` are inverse on `s` and `t`, `f` maps `s` into `t`, and `f'` maps `t`
into `s`, then `f` is a bijection between `s` and `t`. The `maps_to` arguments can be deduced from
`surj_on` statements using `left_inv_on.maps_to` and `right_inv_on.maps_to`. -/
theorem InvOn.bijOn (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : MapsTo f' t s) : BijOn f s t :=
  ⟨hf, h.left.InjOn, h.right.SurjOn hf'⟩
#align set.inv_on.bij_on Set.InvOn.bijOn
-/

#print Set.BijOn.symm /-
theorem BijOn.symm {g : β → α} (h : InvOn f g t s) (hf : BijOn f s t) : BijOn g t s :=
  ⟨h.2.MapsTo hf.SurjOn, h.1.InjOn, h.2.SurjOn hf.MapsTo⟩
#align set.bij_on.symm Set.BijOn.symm
-/

#print Set.bijOn_comm /-
theorem bijOn_comm {g : β → α} (h : InvOn f g t s) : BijOn f s t ↔ BijOn g t s :=
  ⟨BijOn.symm h, BijOn.symm h.symm⟩
#align set.bij_on_comm Set.bijOn_comm
-/

end Set

/-! ### `inv_fun_on` is a left/right inverse -/


namespace Function

variable [Nonempty α] {s : Set α} {f : α → β} {a : α} {b : β}

attribute [local instance 10] Classical.propDecidable

#print Function.invFunOn /-
/-- Construct the inverse for a function `f` on domain `s`. This function is a right inverse of `f`
on `f '' s`. For a computable version, see `function.injective.inv_of_mem_range`. -/
noncomputable def invFunOn (f : α → β) (s : Set α) (b : β) : α :=
  if h : ∃ a, a ∈ s ∧ f a = b then Classical.choose h else Classical.choice ‹Nonempty α›
#align function.inv_fun_on Function.invFunOn
-/

#print Function.invFunOn_pos /-
theorem invFunOn_pos (h : ∃ a ∈ s, f a = b) : invFunOn f s b ∈ s ∧ f (invFunOn f s b) = b := by
  rw [bex_def] at h <;> rw [inv_fun_on, dif_pos h] <;> exact Classical.choose_spec h
#align function.inv_fun_on_pos Function.invFunOn_pos
-/

#print Function.invFunOn_mem /-
theorem invFunOn_mem (h : ∃ a ∈ s, f a = b) : invFunOn f s b ∈ s :=
  (invFunOn_pos h).left
#align function.inv_fun_on_mem Function.invFunOn_mem
-/

#print Function.invFunOn_eq /-
theorem invFunOn_eq (h : ∃ a ∈ s, f a = b) : f (invFunOn f s b) = b :=
  (invFunOn_pos h).right
#align function.inv_fun_on_eq Function.invFunOn_eq
-/

#print Function.invFunOn_neg /-
theorem invFunOn_neg (h : ¬∃ a ∈ s, f a = b) : invFunOn f s b = Classical.choice ‹Nonempty α› := by
  rw [bex_def] at h <;> rw [inv_fun_on, dif_neg h]
#align function.inv_fun_on_neg Function.invFunOn_neg
-/

#print Function.invFunOn_apply_mem /-
@[simp]
theorem invFunOn_apply_mem (h : a ∈ s) : invFunOn f s (f a) ∈ s :=
  invFunOn_mem ⟨a, h, rfl⟩
#align function.inv_fun_on_apply_mem Function.invFunOn_apply_mem
-/

#print Function.invFunOn_apply_eq /-
theorem invFunOn_apply_eq (h : a ∈ s) : f (invFunOn f s (f a)) = f a :=
  invFunOn_eq ⟨a, h, rfl⟩
#align function.inv_fun_on_apply_eq Function.invFunOn_apply_eq
-/

end Function

open Function

namespace Set

variable {s s₁ s₂ : Set α} {t : Set β} {f : α → β}

#print Set.InjOn.leftInvOn_invFunOn /-
theorem InjOn.leftInvOn_invFunOn [Nonempty α] (h : InjOn f s) : LeftInvOn (invFunOn f s) f s :=
  fun a ha => h (invFunOn_apply_mem ha) ha (invFunOn_apply_eq ha)
#align set.inj_on.left_inv_on_inv_fun_on Set.InjOn.leftInvOn_invFunOn
-/

#print Set.InjOn.invFunOn_image /-
theorem InjOn.invFunOn_image [Nonempty α] (h : InjOn f s₂) (ht : s₁ ⊆ s₂) :
    invFunOn f s₂ '' (f '' s₁) = s₁ :=
  h.leftInvOn_invFunOn.image_image' ht
#align set.inj_on.inv_fun_on_image Set.InjOn.invFunOn_image
-/

#print Set.SurjOn.rightInvOn_invFunOn /-
theorem SurjOn.rightInvOn_invFunOn [Nonempty α] (h : SurjOn f s t) :
    RightInvOn (invFunOn f s) f t := fun y hy => invFunOn_eq <| mem_image_iff_bex.1 <| h hy
#align set.surj_on.right_inv_on_inv_fun_on Set.SurjOn.rightInvOn_invFunOn
-/

#print Set.BijOn.invOn_invFunOn /-
theorem BijOn.invOn_invFunOn [Nonempty α] (h : BijOn f s t) : InvOn (invFunOn f s) f s t :=
  ⟨h.InjOn.leftInvOn_invFunOn, h.SurjOn.rightInvOn_invFunOn⟩
#align set.bij_on.inv_on_inv_fun_on Set.BijOn.invOn_invFunOn
-/

#print Set.SurjOn.invOn_invFunOn /-
theorem SurjOn.invOn_invFunOn [Nonempty α] (h : SurjOn f s t) :
    InvOn (invFunOn f s) f (invFunOn f s '' t) t :=
  by
  refine' ⟨_, h.right_inv_on_inv_fun_on⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [h.right_inv_on_inv_fun_on hy]
#align set.surj_on.inv_on_inv_fun_on Set.SurjOn.invOn_invFunOn
-/

#print Set.SurjOn.mapsTo_invFunOn /-
theorem SurjOn.mapsTo_invFunOn [Nonempty α] (h : SurjOn f s t) : MapsTo (invFunOn f s) t s :=
  fun y hy => mem_preimage.2 <| invFunOn_mem <| mem_image_iff_bex.1 <| h hy
#align set.surj_on.maps_to_inv_fun_on Set.SurjOn.mapsTo_invFunOn
-/

#print Set.SurjOn.bijOn_subset /-
theorem SurjOn.bijOn_subset [Nonempty α] (h : SurjOn f s t) : BijOn f (invFunOn f s '' t) t :=
  by
  refine' h.inv_on_inv_fun_on.bij_on _ (maps_to_image _ _)
  rintro _ ⟨y, hy, rfl⟩
  rwa [h.right_inv_on_inv_fun_on hy]
#align set.surj_on.bij_on_subset Set.SurjOn.bijOn_subset
-/

/- ././././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (s' «expr ⊆ » s) -/
#print Set.surjOn_iff_exists_bijOn_subset /-
theorem surjOn_iff_exists_bijOn_subset : SurjOn f s t ↔ ∃ (s' : _) (_ : s' ⊆ s), BijOn f s' t :=
  by
  constructor
  · rcases eq_empty_or_nonempty t with (rfl | ht)
    · exact fun _ => ⟨∅, empty_subset _, bij_on_empty f⟩
    · intro h
      haveI : Nonempty α := ⟨Classical.choose (h.comap_nonempty ht)⟩
      exact ⟨_, h.maps_to_inv_fun_on.image_subset, h.bij_on_subset⟩
  · rintro ⟨s', hs', hfs'⟩
    exact hfs'.surj_on.mono hs' (subset.refl _)
#align set.surj_on_iff_exists_bij_on_subset Set.surjOn_iff_exists_bijOn_subset
-/

#print Set.preimage_invFun_of_mem /-
theorem preimage_invFun_of_mem [n : Nonempty α] {f : α → β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n ∈ s) : invFun f ⁻¹' s = f '' s ∪ range fᶜ :=
  by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · simp [left_inverse_inv_fun hf _, hf.mem_set_image]
  · simp [mem_preimage, inv_fun_neg hx, h, hx]
#align set.preimage_inv_fun_of_mem Set.preimage_invFun_of_mem
-/

#print Set.preimage_invFun_of_not_mem /-
theorem preimage_invFun_of_not_mem [n : Nonempty α] {f : α → β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n ∉ s) : invFun f ⁻¹' s = f '' s :=
  by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · rw [mem_preimage, left_inverse_inv_fun hf, hf.mem_set_image]
  · have : x ∉ f '' s := fun h' => hx (image_subset_range _ _ h')
    simp only [mem_preimage, inv_fun_neg hx, h, this]
#align set.preimage_inv_fun_of_not_mem Set.preimage_invFun_of_not_mem
-/

end Set

/-! ### Monotone -/


namespace Monotone

variable [Preorder α] [Preorder β] {f : α → β}

#print Monotone.restrict /-
protected theorem restrict (h : Monotone f) (s : Set α) : Monotone (s.restrict f) := fun x y hxy =>
  h hxy
#align monotone.restrict Monotone.restrict
-/

#print Monotone.codRestrict /-
protected theorem codRestrict (h : Monotone f) {s : Set β} (hs : ∀ x, f x ∈ s) :
    Monotone (s.codRestrict f hs) :=
  h
#align monotone.cod_restrict Monotone.codRestrict
-/

#print Monotone.rangeFactorization /-
protected theorem rangeFactorization (h : Monotone f) : Monotone (Set.rangeFactorization f) :=
  h
#align monotone.range_factorization Monotone.rangeFactorization
-/

end Monotone

/-! ### Piecewise defined function -/


namespace Set

variable {δ : α → Sort y} (s : Set α) (f g : ∀ i, δ i)

#print Set.piecewise_empty /-
@[simp]
theorem piecewise_empty [∀ i : α, Decidable (i ∈ (∅ : Set α))] : piecewise ∅ f g = g := by ext i;
  simp [piecewise]
#align set.piecewise_empty Set.piecewise_empty
-/

#print Set.piecewise_univ /-
@[simp]
theorem piecewise_univ [∀ i : α, Decidable (i ∈ (Set.univ : Set α))] : piecewise Set.univ f g = f :=
  by ext i; simp [piecewise]
#align set.piecewise_univ Set.piecewise_univ
-/

#print Set.piecewise_insert_self /-
@[simp]
theorem piecewise_insert_self {j : α} [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g j = f j := by simp [piecewise]
#align set.piecewise_insert_self Set.piecewise_insert_self
-/

variable [∀ j, Decidable (j ∈ s)]

#print Set.Compl.decidableMem /-
instance Compl.decidableMem (j : α) : Decidable (j ∈ sᶜ) :=
  Not.decidable
#align set.compl.decidable_mem Set.Compl.decidableMem
-/

#print Set.piecewise_insert /-
theorem piecewise_insert [DecidableEq α] (j : α) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g = Function.update (s.piecewise f g) j (f j) :=
  by
  simp [piecewise]
  ext i
  by_cases h : i = j
  · rw [h]; simp
  · by_cases h' : i ∈ s <;> simp [h, h']
#align set.piecewise_insert Set.piecewise_insert
-/

#print Set.piecewise_eq_of_mem /-
@[simp]
theorem piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i :=
  if_pos hi
#align set.piecewise_eq_of_mem Set.piecewise_eq_of_mem
-/

#print Set.piecewise_eq_of_not_mem /-
@[simp]
theorem piecewise_eq_of_not_mem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i :=
  if_neg hi
#align set.piecewise_eq_of_not_mem Set.piecewise_eq_of_not_mem
-/

#print Set.piecewise_singleton /-
theorem piecewise_singleton (x : α) [∀ y, Decidable (y ∈ ({x} : Set α))] [DecidableEq α]
    (f g : α → β) : piecewise {x} f g = Function.update g x (f x) := by ext y; by_cases hy : y = x;
  · subst y; simp; · simp [hy]
#align set.piecewise_singleton Set.piecewise_singleton
-/

#print Set.piecewise_eqOn /-
theorem piecewise_eqOn (f g : α → β) : EqOn (s.piecewise f g) f s := fun _ =>
  piecewise_eq_of_mem _ _ _
#align set.piecewise_eq_on Set.piecewise_eqOn
-/

#print Set.piecewise_eqOn_compl /-
theorem piecewise_eqOn_compl (f g : α → β) : EqOn (s.piecewise f g) g (sᶜ) := fun _ =>
  piecewise_eq_of_not_mem _ _ _
#align set.piecewise_eq_on_compl Set.piecewise_eqOn_compl
-/

/- ././././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (i «expr ∉ » s) -/
#print Set.piecewise_le /-
theorem piecewise_le {δ : α → Type _} [∀ i, Preorder (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)]
    {f₁ f₂ g : ∀ i, δ i} (h₁ : ∀ i ∈ s, f₁ i ≤ g i) (h₂ : ∀ (i) (_ : i ∉ s), f₂ i ≤ g i) :
    s.piecewise f₁ f₂ ≤ g := fun i => if h : i ∈ s then by simp [*] else by simp [*]
#align set.piecewise_le Set.piecewise_le
-/

/- ././././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (i «expr ∉ » s) -/
#print Set.le_piecewise /-
theorem le_piecewise {δ : α → Type _} [∀ i, Preorder (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)]
    {f₁ f₂ g : ∀ i, δ i} (h₁ : ∀ i ∈ s, g i ≤ f₁ i) (h₂ : ∀ (i) (_ : i ∉ s), g i ≤ f₂ i) :
    g ≤ s.piecewise f₁ f₂ :=
  @piecewise_le α (fun i => (δ i)ᵒᵈ) _ s _ _ _ _ h₁ h₂
#align set.le_piecewise Set.le_piecewise
-/

/- ././././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (i «expr ∉ » s) -/
#print Set.piecewise_le_piecewise /-
theorem piecewise_le_piecewise {δ : α → Type _} [∀ i, Preorder (δ i)] {s : Set α}
    [∀ j, Decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : ∀ i, δ i} (h₁ : ∀ i ∈ s, f₁ i ≤ g₁ i)
    (h₂ : ∀ (i) (_ : i ∉ s), f₂ i ≤ g₂ i) : s.piecewise f₁ f₂ ≤ s.piecewise g₁ g₂ := by
  apply piecewise_le <;> intros <;> simp [*]
#align set.piecewise_le_piecewise Set.piecewise_le_piecewise
-/

#print Set.piecewise_insert_of_ne /-
@[simp]
theorem piecewise_insert_of_ne {i j : α} (h : i ≠ j) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g i = s.piecewise f g i := by simp [piecewise, h]
#align set.piecewise_insert_of_ne Set.piecewise_insert_of_ne
-/

#print Set.piecewise_compl /-
@[simp]
theorem piecewise_compl [∀ i, Decidable (i ∈ sᶜ)] : sᶜ.piecewise f g = s.piecewise g f :=
  funext fun x => if hx : x ∈ s then by simp [hx] else by simp [hx]
#align set.piecewise_compl Set.piecewise_compl
-/

#print Set.piecewise_range_comp /-
@[simp]
theorem piecewise_range_comp {ι : Sort _} (f : ι → α) [∀ j, Decidable (j ∈ range f)]
    (g₁ g₂ : α → β) : (range f).piecewise g₁ g₂ ∘ f = g₁ ∘ f :=
  EqOn.comp_eq <| piecewise_eqOn _ _ _
#align set.piecewise_range_comp Set.piecewise_range_comp
-/

#print Set.MapsTo.piecewise_ite /-
theorem MapsTo.piecewise_ite {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {f₁ f₂ : α → β}
    [∀ i, Decidable (i ∈ s)] (h₁ : MapsTo f₁ (s₁ ∩ s) (t₁ ∩ t))
    (h₂ : MapsTo f₂ (s₂ ∩ sᶜ) (t₂ ∩ tᶜ)) : MapsTo (s.piecewise f₁ f₂) (s.ite s₁ s₂) (t.ite t₁ t₂) :=
  by
  refine' (h₁.congr _).union_union (h₂.congr _)
  exacts [(piecewise_eq_on s f₁ f₂).symm.mono (inter_subset_right _ _),
    (piecewise_eq_on_compl s f₁ f₂).symm.mono (inter_subset_right _ _)]
#align set.maps_to.piecewise_ite Set.MapsTo.piecewise_ite
-/

#print Set.eqOn_piecewise /-
theorem eqOn_piecewise {f f' g : α → β} {t} :
    EqOn (s.piecewise f f') g t ↔ EqOn f g (t ∩ s) ∧ EqOn f' g (t ∩ sᶜ) :=
  by
  simp only [eq_on, ← forall_and]
  refine' forall_congr' fun a => _; by_cases a ∈ s <;> simp [*]
#align set.eq_on_piecewise Set.eqOn_piecewise
-/

#print Set.EqOn.piecewise_ite' /-
theorem EqOn.piecewise_ite' {f f' g : α → β} {t t'} (h : EqOn f g (t ∩ s))
    (h' : EqOn f' g (t' ∩ sᶜ)) : EqOn (s.piecewise f f') g (s.ite t t') := by
  simp [eq_on_piecewise, *]
#align set.eq_on.piecewise_ite' Set.EqOn.piecewise_ite'
-/

#print Set.EqOn.piecewise_ite /-
theorem EqOn.piecewise_ite {f f' g : α → β} {t t'} (h : EqOn f g t) (h' : EqOn f' g t') :
    EqOn (s.piecewise f f') g (s.ite t t') :=
  (h.mono (inter_subset_left _ _)).piecewise_ite' s (h'.mono (inter_subset_left _ _))
#align set.eq_on.piecewise_ite Set.EqOn.piecewise_ite
-/

#print Set.piecewise_preimage /-
theorem piecewise_preimage (f g : α → β) (t) : s.piecewise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t) :=
  ext fun x => by by_cases x ∈ s <;> simp [*, Set.ite]
#align set.piecewise_preimage Set.piecewise_preimage
-/

#print Set.apply_piecewise /-
theorem apply_piecewise {δ' : α → Sort _} (h : ∀ i, δ i → δ' i) {x : α} :
    h x (s.piecewise f g x) = s.piecewise (fun x => h x (f x)) (fun x => h x (g x)) x := by
  by_cases hx : x ∈ s <;> simp [hx]
#align set.apply_piecewise Set.apply_piecewise
-/

#print Set.apply_piecewise₂ /-
theorem apply_piecewise₂ {δ' δ'' : α → Sort _} (f' g' : ∀ i, δ' i) (h : ∀ i, δ i → δ' i → δ'' i)
    {x : α} :
    h x (s.piecewise f g x) (s.piecewise f' g' x) =
      s.piecewise (fun x => h x (f x) (f' x)) (fun x => h x (g x) (g' x)) x :=
  by by_cases hx : x ∈ s <;> simp [hx]
#align set.apply_piecewise₂ Set.apply_piecewise₂
-/

#print Set.piecewise_op /-
theorem piecewise_op {δ' : α → Sort _} (h : ∀ i, δ i → δ' i) :
    (s.piecewise (fun x => h x (f x)) fun x => h x (g x)) = fun x => h x (s.piecewise f g x) :=
  funext fun x => (apply_piecewise _ _ _ _).symm
#align set.piecewise_op Set.piecewise_op
-/

#print Set.piecewise_op₂ /-
theorem piecewise_op₂ {δ' δ'' : α → Sort _} (f' g' : ∀ i, δ' i) (h : ∀ i, δ i → δ' i → δ'' i) :
    (s.piecewise (fun x => h x (f x) (f' x)) fun x => h x (g x) (g' x)) = fun x =>
      h x (s.piecewise f g x) (s.piecewise f' g' x) :=
  funext fun x => (apply_piecewise₂ _ _ _ _ _ _).symm
#align set.piecewise_op₂ Set.piecewise_op₂
-/

#print Set.piecewise_same /-
@[simp]
theorem piecewise_same : s.piecewise f f = f := by ext x; by_cases hx : x ∈ s <;> simp [hx]
#align set.piecewise_same Set.piecewise_same
-/

#print Set.range_piecewise /-
theorem range_piecewise (f g : α → β) : range (s.piecewise f g) = f '' s ∪ g '' sᶜ :=
  by
  ext y; constructor
  · rintro ⟨x, rfl⟩; by_cases h : x ∈ s <;> [left; right] <;> use x <;> simp [h]
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> use x <;> simp_all
#align set.range_piecewise Set.range_piecewise
-/

/- ././././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (y «expr ∉ » s) -/
#print Set.injective_piecewise_iff /-
theorem injective_piecewise_iff {f g : α → β} :
    Injective (s.piecewise f g) ↔
      InjOn f s ∧ InjOn g (sᶜ) ∧ ∀ x ∈ s, ∀ (y) (_ : y ∉ s), f x ≠ g y :=
  by
  rw [injective_iff_inj_on_univ, ← union_compl_self s, inj_on_union (@disjoint_compl_right _ _ s),
    (piecewise_eq_on s f g).injOn_iff, (piecewise_eq_on_compl s f g).injOn_iff]
  refine' and_congr Iff.rfl (and_congr Iff.rfl <| forall₄_congr fun x hx y hy => _)
  rw [piecewise_eq_of_mem s f g hx, piecewise_eq_of_not_mem s f g hy]
#align set.injective_piecewise_iff Set.injective_piecewise_iff
-/

#print Set.piecewise_mem_pi /-
theorem piecewise_mem_pi {δ : α → Type _} {t : Set α} {t' : ∀ i, Set (δ i)} {f g} (hf : f ∈ pi t t')
    (hg : g ∈ pi t t') : s.piecewise f g ∈ pi t t' := by intro i ht;
  by_cases hs : i ∈ s <;> simp [hf i ht, hg i ht, hs]
#align set.piecewise_mem_pi Set.piecewise_mem_pi
-/

#print Set.pi_piecewise /-
@[simp]
theorem pi_piecewise {ι : Type _} {α : ι → Type _} (s s' : Set ι) (t t' : ∀ i, Set (α i))
    [∀ x, Decidable (x ∈ s')] : pi s (s'.piecewise t t') = pi (s ∩ s') t ∩ pi (s \ s') t' :=
  by
  ext x
  simp only [mem_pi, mem_inter_iff, ← forall_and]
  refine' forall_congr' fun i => _
  by_cases hi : i ∈ s' <;> simp [*]
#align set.pi_piecewise Set.pi_piecewise
-/

#print Set.univ_pi_piecewise_univ /-
theorem univ_pi_piecewise_univ {ι : Type _} {α : ι → Type _} (s : Set ι) (t : ∀ i, Set (α i))
    [∀ x, Decidable (x ∈ s)] : pi univ (s.piecewise t fun _ => univ) = pi s t := by simp
#align set.univ_pi_piecewise Set.univ_pi_piecewise_univ
-/

end Set

open Set

#print StrictMonoOn.injOn /-
theorem StrictMonoOn.injOn [LinearOrder α] [Preorder β] {f : α → β} {s : Set α}
    (H : StrictMonoOn f s) : s.InjOn f := fun x hx y hy hxy =>
  show Ordering.eq.Compares x y from (H.Compares hx hy).1 hxy
#align strict_mono_on.inj_on StrictMonoOn.injOn
-/

#print StrictAntiOn.injOn /-
theorem StrictAntiOn.injOn [LinearOrder α] [Preorder β] {f : α → β} {s : Set α}
    (H : StrictAntiOn f s) : s.InjOn f :=
  @StrictMonoOn.injOn α βᵒᵈ _ _ f s H
#align strict_anti_on.inj_on StrictAntiOn.injOn
-/

#print StrictMonoOn.comp /-
theorem StrictMonoOn.comp [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β} {s : Set α}
    {t : Set β} (hg : StrictMonoOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t) :
    StrictMonoOn (g ∘ f) s := fun x hx y hy hxy => hg (hs hx) (hs hy) <| hf hx hy hxy
#align strict_mono_on.comp StrictMonoOn.comp
-/

#print StrictMonoOn.comp_strictAntiOn /-
theorem StrictMonoOn.comp_strictAntiOn [Preorder α] [Preorder β] [Preorder γ] {g : β → γ}
    {f : α → β} {s : Set α} {t : Set β} (hg : StrictMonoOn g t) (hf : StrictAntiOn f s)
    (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s := fun x hx y hy hxy =>
  hg (hs hy) (hs hx) <| hf hx hy hxy
#align strict_mono_on.comp_strict_anti_on StrictMonoOn.comp_strictAntiOn
-/

#print StrictAntiOn.comp /-
theorem StrictAntiOn.comp [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β} {s : Set α}
    {t : Set β} (hg : StrictAntiOn g t) (hf : StrictAntiOn f s) (hs : Set.MapsTo f s t) :
    StrictMonoOn (g ∘ f) s := fun x hx y hy hxy => hg (hs hy) (hs hx) <| hf hx hy hxy
#align strict_anti_on.comp StrictAntiOn.comp
-/

#print StrictAntiOn.comp_strictMonoOn /-
theorem StrictAntiOn.comp_strictMonoOn [Preorder α] [Preorder β] [Preorder γ] {g : β → γ}
    {f : α → β} {s : Set α} {t : Set β} (hg : StrictAntiOn g t) (hf : StrictMonoOn f s)
    (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s := fun x hx y hy hxy =>
  hg (hs hx) (hs hy) <| hf hx hy hxy
#align strict_anti_on.comp_strict_mono_on StrictAntiOn.comp_strictMonoOn
-/

#print strictMono_restrict /-
@[simp]
theorem strictMono_restrict [Preorder α] [Preorder β] {f : α → β} {s : Set α} :
    StrictMono (s.restrict f) ↔ StrictMonoOn f s := by simp [Set.restrict, StrictMono, StrictMonoOn]
#align strict_mono_restrict strictMono_restrict
-/

alias ⟨_root_.strict_mono.of_restrict, _root_.strict_mono_on.restrict⟩ := strictMono_restrict
#align strict_mono.of_restrict StrictMono.of_restrict
#align strict_mono_on.restrict StrictMonoOn.restrict

#print StrictMono.codRestrict /-
theorem StrictMono.codRestrict [Preorder α] [Preorder β] {f : α → β} (hf : StrictMono f) {s : Set β}
    (hs : ∀ x, f x ∈ s) : StrictMono (Set.codRestrict f s hs) :=
  hf
#align strict_mono.cod_restrict StrictMono.codRestrict
-/

namespace Function

open Set

variable {fa : α → α} {fb : β → β} {f : α → β} {g : β → γ} {s t : Set α}

#print Function.Injective.comp_injOn /-
theorem Injective.comp_injOn (hg : Injective g) (hf : s.InjOn f) : s.InjOn (g ∘ f) :=
  (hg.InjOn univ).comp hf (mapsTo_univ _ _)
#align function.injective.comp_inj_on Function.Injective.comp_injOn
-/

#print Function.Surjective.surjOn /-
theorem Surjective.surjOn (hf : Surjective f) (s : Set β) : SurjOn f univ s :=
  (surjective_iff_surjOn_univ.1 hf).mono (Subset.refl _) (subset_univ _)
#align function.surjective.surj_on Function.Surjective.surjOn
-/

#print Function.LeftInverse.leftInvOn /-
theorem LeftInverse.leftInvOn {g : β → α} (h : LeftInverse f g) (s : Set β) : LeftInvOn f g s :=
  fun x hx => h x
#align function.left_inverse.left_inv_on Function.LeftInverse.leftInvOn
-/

#print Function.RightInverse.rightInvOn /-
theorem RightInverse.rightInvOn {g : β → α} (h : RightInverse f g) (s : Set α) : RightInvOn f g s :=
  fun x hx => h x
#align function.right_inverse.right_inv_on Function.RightInverse.rightInvOn
-/

#print Function.LeftInverse.rightInvOn_range /-
theorem LeftInverse.rightInvOn_range {g : β → α} (h : LeftInverse f g) : RightInvOn f g (range g) :=
  forall_mem_range.2 fun i => congr_arg g (h i)
#align function.left_inverse.right_inv_on_range Function.LeftInverse.rightInvOn_range
-/

namespace Semiconj

#print Function.Semiconj.mapsTo_image /-
theorem mapsTo_image (h : Semiconj f fa fb) (ha : MapsTo fa s t) : MapsTo fb (f '' s) (f '' t) :=
  fun y ⟨x, hx, hy⟩ => hy ▸ ⟨fa x, ha hx, h x⟩
#align function.semiconj.maps_to_image Function.Semiconj.mapsTo_image
-/

#print Function.Semiconj.mapsTo_range /-
theorem mapsTo_range (h : Semiconj f fa fb) : MapsTo fb (range f) (range f) := fun y ⟨x, hy⟩ =>
  hy ▸ ⟨fa x, h x⟩
#align function.semiconj.maps_to_range Function.Semiconj.mapsTo_range
-/

#print Function.Semiconj.surjOn_image /-
theorem surjOn_image (h : Semiconj f fa fb) (ha : SurjOn fa s t) : SurjOn fb (f '' s) (f '' t) :=
  by
  rintro y ⟨x, hxt, rfl⟩
  rcases ha hxt with ⟨x, hxs, rfl⟩
  rw [h x]
  exact mem_image_of_mem _ (mem_image_of_mem _ hxs)
#align function.semiconj.surj_on_image Function.Semiconj.surjOn_image
-/

#print Function.Semiconj.surjOn_range /-
theorem surjOn_range (h : Semiconj f fa fb) (ha : Surjective fa) : SurjOn fb (range f) (range f) :=
  by rw [← image_univ]; exact h.surj_on_image (ha.surj_on univ)
#align function.semiconj.surj_on_range Function.Semiconj.surjOn_range
-/

#print Function.Semiconj.injOn_image /-
theorem injOn_image (h : Semiconj f fa fb) (ha : InjOn fa s) (hf : InjOn f (fa '' s)) :
    InjOn fb (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ H
  simp only [← h.eq] at H
  exact congr_arg f (ha hx hy <| hf (mem_image_of_mem fa hx) (mem_image_of_mem fa hy) H)
#align function.semiconj.inj_on_image Function.Semiconj.injOn_image
-/

#print Function.Semiconj.injOn_range /-
theorem injOn_range (h : Semiconj f fa fb) (ha : Injective fa) (hf : InjOn f (range fa)) :
    InjOn fb (range f) := by rw [← image_univ] at *; exact h.inj_on_image (ha.inj_on univ) hf
#align function.semiconj.inj_on_range Function.Semiconj.injOn_range
-/

#print Function.Semiconj.bijOn_image /-
theorem bijOn_image (h : Semiconj f fa fb) (ha : BijOn fa s t) (hf : InjOn f t) :
    BijOn fb (f '' s) (f '' t) :=
  ⟨h.mapsTo_image ha.MapsTo, h.injOn_image ha.InjOn (ha.image_eq.symm ▸ hf),
    h.surjOn_image ha.SurjOn⟩
#align function.semiconj.bij_on_image Function.Semiconj.bijOn_image
-/

#print Function.Semiconj.bijOn_range /-
theorem bijOn_range (h : Semiconj f fa fb) (ha : Bijective fa) (hf : Injective f) :
    BijOn fb (range f) (range f) := by
  rw [← image_univ]
  exact h.bij_on_image (bijective_iff_bij_on_univ.1 ha) (hf.inj_on univ)
#align function.semiconj.bij_on_range Function.Semiconj.bijOn_range
-/

#print Function.Semiconj.mapsTo_preimage /-
theorem mapsTo_preimage (h : Semiconj f fa fb) {s t : Set β} (hb : MapsTo fb s t) :
    MapsTo fa (f ⁻¹' s) (f ⁻¹' t) := fun x hx => by simp only [mem_preimage, h x, hb hx]
#align function.semiconj.maps_to_preimage Function.Semiconj.mapsTo_preimage
-/

#print Function.Semiconj.injOn_preimage /-
theorem injOn_preimage (h : Semiconj f fa fb) {s : Set β} (hb : InjOn fb s)
    (hf : InjOn f (f ⁻¹' s)) : InjOn fa (f ⁻¹' s) :=
  by
  intro x hx y hy H
  have := congr_arg f H
  rw [h.eq, h.eq] at this
  exact hf hx hy (hb hx hy this)
#align function.semiconj.inj_on_preimage Function.Semiconj.injOn_preimage
-/

end Semiconj

#print Function.update_comp_eq_of_not_mem_range' /-
theorem update_comp_eq_of_not_mem_range' {α β : Sort _} {γ : β → Sort _} [DecidableEq β]
    (g : ∀ b, γ b) {f : α → β} {i : β} (a : γ i) (h : i ∉ Set.range f) :
    (fun j => (Function.update g i a) (f j)) = fun j => g (f j) :=
  update_comp_eq_of_forall_ne' _ _ fun x hx => h ⟨x, hx⟩
#align function.update_comp_eq_of_not_mem_range' Function.update_comp_eq_of_not_mem_range'
-/

#print Function.update_comp_eq_of_not_mem_range /-
/-- Non-dependent version of `function.update_comp_eq_of_not_mem_range'` -/
theorem update_comp_eq_of_not_mem_range {α β γ : Sort _} [DecidableEq β] (g : β → γ) {f : α → β}
    {i : β} (a : γ) (h : i ∉ Set.range f) : Function.update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_not_mem_range' g a h
#align function.update_comp_eq_of_not_mem_range Function.update_comp_eq_of_not_mem_range
-/

#print Function.insert_injOn /-
theorem insert_injOn (s : Set α) : sᶜ.InjOn fun a => insert a s := fun a ha b _ => (insert_inj ha).1
#align function.insert_inj_on Function.insert_injOn
-/

#print Function.monotoneOn_of_rightInvOn_of_mapsTo /-
theorem monotoneOn_of_rightInvOn_of_mapsTo [PartialOrder α] [LinearOrder β] {φ : β → α} {ψ : α → β}
    {t : Set β} {s : Set α} (hφ : MonotoneOn φ t) (φψs : Set.RightInvOn ψ φ s)
    (ψts : Set.MapsTo ψ s t) : MonotoneOn ψ s :=
  by
  rintro x xs y ys l
  rcases le_total (ψ x) (ψ y) with (ψxy | ψyx)
  · exact ψxy
  · cases le_antisymm l (φψs.eq ys ▸ φψs.eq xs ▸ hφ (ψts ys) (ψts xs) ψyx); rfl
#align function.monotone_on_of_right_inv_on_of_maps_to Function.monotoneOn_of_rightInvOn_of_mapsTo
-/

#print Function.antitoneOn_of_rightInvOn_of_mapsTo /-
theorem antitoneOn_of_rightInvOn_of_mapsTo [PartialOrder α] [LinearOrder β] {φ : β → α} {ψ : α → β}
    {t : Set β} {s : Set α} (hφ : AntitoneOn φ t) (φψs : Set.RightInvOn ψ φ s)
    (ψts : Set.MapsTo ψ s t) : AntitoneOn ψ s :=
  (monotoneOn_of_rightInvOn_of_mapsTo hφ.dual_left φψs ψts).dual_right
#align function.antitone_on_of_right_inv_on_of_maps_to Function.antitoneOn_of_rightInvOn_of_mapsTo
-/

end Function

/-! ### Equivalences, permutations -/


namespace Set

variable {p : β → Prop} [DecidablePred p] {f : α ≃ Subtype p} {g g₁ g₂ : Perm α} {s t : Set α}

#print Set.MapsTo.extendDomain /-
protected theorem MapsTo.extendDomain (h : MapsTo g s t) :
    MapsTo (g.extendDomain f) (coe ∘ f '' s) (coe ∘ f '' t) := by rintro _ ⟨a, ha, rfl⟩;
  exact ⟨_, h ha, by rw [extend_domain_apply_image]⟩
#align set.maps_to.extend_domain Set.MapsTo.extendDomain
-/

#print Set.SurjOn.extendDomain /-
protected theorem SurjOn.extendDomain (h : SurjOn g s t) :
    SurjOn (g.extendDomain f) (coe ∘ f '' s) (coe ∘ f '' t) :=
  by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, rfl⟩ := h ha
  exact ⟨_, ⟨_, hb, rfl⟩, by rw [extend_domain_apply_image]⟩
#align set.surj_on.extend_domain Set.SurjOn.extendDomain
-/

#print Set.BijOn.extendDomain /-
protected theorem BijOn.extendDomain (h : Set.BijOn g s t) :
    BijOn (g.extendDomain f) (coe ∘ f '' s) (coe ∘ f '' t) :=
  ⟨h.MapsTo.extendDomain, (g.extendDomain f).Injective.InjOn _, h.SurjOn.extendDomain⟩
#align set.bij_on.extend_domain Set.BijOn.extendDomain
-/

#print Set.LeftInvOn.extendDomain /-
protected theorem LeftInvOn.extendDomain (h : LeftInvOn g₁ g₂ s) :
    LeftInvOn (g₁.extendDomain f) (g₂.extendDomain f) (coe ∘ f '' s) := by rintro _ ⟨a, ha, rfl⟩;
  simp_rw [extend_domain_apply_image, h ha]
#align set.left_inv_on.extend_domain Set.LeftInvOn.extendDomain
-/

#print Set.RightInvOn.extendDomain /-
protected theorem RightInvOn.extendDomain (h : RightInvOn g₁ g₂ t) :
    RightInvOn (g₁.extendDomain f) (g₂.extendDomain f) (coe ∘ f '' t) := by rintro _ ⟨a, ha, rfl⟩;
  simp_rw [extend_domain_apply_image, h ha]
#align set.right_inv_on.extend_domain Set.RightInvOn.extendDomain
-/

#print Set.InvOn.extendDomain /-
protected theorem InvOn.extendDomain (h : InvOn g₁ g₂ s t) :
    InvOn (g₁.extendDomain f) (g₂.extendDomain f) (coe ∘ f '' s) (coe ∘ f '' t) :=
  ⟨h.1.extendDomain, h.2.extendDomain⟩
#align set.inv_on.extend_domain Set.InvOn.extendDomain
-/

end Set

namespace Equiv

variable (e : α ≃ β) {s : Set α} {t : Set β}

#print Equiv.bijOn' /-
theorem bijOn' (h₁ : MapsTo e s t) (h₂ : MapsTo e.symm t s) : BijOn e s t :=
  ⟨h₁, e.Injective.InjOn _, fun b hb => ⟨e.symm b, h₂ hb, apply_symm_apply _ _⟩⟩
#align equiv.bij_on' Equiv.bijOn'
-/

#print Equiv.bijOn /-
protected theorem bijOn (h : ∀ a, e a ∈ t ↔ a ∈ s) : BijOn e s t :=
  e.bijOn' (fun a => (h _).2) fun b hb => (h _).1 <| by rwa [apply_symm_apply]
#align equiv.bij_on Equiv.bijOn
-/

#print Equiv.invOn /-
theorem invOn : InvOn e e.symm t s :=
  ⟨e.rightInverse_symm.LeftInvOn _, e.leftInverse_symm.LeftInvOn _⟩
#align equiv.inv_on Equiv.invOn
-/

#print Equiv.bijOn_image /-
theorem bijOn_image : BijOn e s (e '' s) :=
  (e.Injective.InjOn _).bijOn_image
#align equiv.bij_on_image Equiv.bijOn_image
-/

#print Equiv.bijOn_symm_image /-
theorem bijOn_symm_image : BijOn e.symm (e '' s) s :=
  e.bijOn_image.symm e.InvOn
#align equiv.bij_on_symm_image Equiv.bijOn_symm_image
-/

variable {e}

#print Equiv.bijOn_symm /-
@[simp]
theorem bijOn_symm : BijOn e.symm t s ↔ BijOn e s t :=
  bijOn_comm e.symm.InvOn
#align equiv.bij_on_symm Equiv.bijOn_symm
-/

alias ⟨_root_.set.bij_on.of_equiv_symm, _root_.set.bij_on.equiv_symm⟩ := bij_on_symm
#align set.bij_on.of_equiv_symm Set.BijOn.of_equiv_symm
#align set.bij_on.equiv_symm Set.BijOn.equiv_symm

variable [DecidableEq α] {a b : α}

#print Equiv.bijOn_swap /-
theorem bijOn_swap (ha : a ∈ s) (hb : b ∈ s) : BijOn (swap a b) s s :=
  (swap a b).BijOn fun x => by
    obtain rfl | hxa := eq_or_ne x a <;> obtain rfl | hxb := eq_or_ne x b <;>
      simp [*, swap_apply_of_ne_of_ne]
#align equiv.bij_on_swap Equiv.bijOn_swap
-/

end Equiv

