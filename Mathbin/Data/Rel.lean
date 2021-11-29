import Mathbin.Order.GaloisConnection

/-!
# Relations

This file defines bundled relations. A relation between `α` and `β` is a function `α → β → Prop`.
Relations are also known as set-valued functions, or partial multifunctions.

## Main declarations

* `rel α β`: Relation between `α` and `β`.
* `rel.inv`: `r.inv` is the `rel β α` obtained by swapping the arguments of `r`.
* `rel.dom`: Domain of a relation. `x ∈ r.dom` iff there exists `y` such that `r x y`.
* `rel.codom`: Codomain, aka range, of a relation. `y ∈ r.codom` iff there exists `x` such that
  `r x y`.
* `rel.comp`: Relation composition. Note that the arguments order follows the `category_theory/`
  one, so `r.comp s x z ↔ ∃ y, r x y ∧ s y z`.
* `rel.image`: Image of a set under a relation. `r.image s` is the set of `f x` over all `x ∈ s`.
* `rel.preimage`: Preimage of a set under a relation. Note that `r.preimage = r.inv.image`.
* `rel.core`: Core of a set. For `s : set β`, `r.core s` is the set of `x : α` such that all `y`
  related to `x` are in `s`.
* `rel.restrict_domain`: Domain-restriction of a relation to a subtype.
* `function.graph`: Graph of a function as a relation.
-/


variable {α β γ : Type _}

-- error in Data.Rel: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler complete_lattice
/-- A relation on `α` and `β`, aka a set-valued function, aka a partial multifunction --/
@[derive #[expr complete_lattice], derive #[expr inhabited]]
def rel (α β : Type*) :=
α → β → exprProp()

namespace Rel

variable {δ : Type _} (r : Rel α β)

/-- The inverse relation : `r.inv x y ↔ r y x`. Note that this is *not* a groupoid inverse. -/
def inv : Rel β α :=
  flip r

theorem inv_def (x : α) (y : β) : r.inv y x ↔ r x y :=
  Iff.rfl

theorem inv_invₓ : inv (inv r) = r :=
  by 
    ext x y 
    rfl

/-- Domain of a relation -/
def dom :=
  { x | ∃ y, r x y }

theorem dom_mono {r s : Rel α β} (h : r ≤ s) : dom r ⊆ dom s :=
  fun a ⟨b, hx⟩ => ⟨b, h a b hx⟩

/-- Codomain aka range of a relation -/
def codom :=
  { y | ∃ x, r x y }

theorem codom_inv : r.inv.codom = r.dom :=
  by 
    ext x y 
    rfl

theorem dom_inv : r.inv.dom = r.codom :=
  by 
    ext x y 
    rfl

/-- Composition of relation; note that it follows the `category_theory/` order of arguments. -/
def comp (r : Rel α β) (s : Rel β γ) : Rel α γ :=
  fun x z => ∃ y, r x y ∧ s y z

local infixr:0 " ∘ " => Rel.Comp

theorem comp_assoc (r : Rel α β) (s : Rel β γ) (t : Rel γ δ) : ((r ∘ s) ∘ t) = (r ∘ s ∘ t) :=
  by 
    unfold comp 
    ext x w 
    split 
    ·
      rintro ⟨z, ⟨y, rxy, syz⟩, tzw⟩
      exact ⟨y, rxy, z, syz, tzw⟩
    rintro ⟨y, rxy, z, syz, tzw⟩
    exact ⟨z, ⟨y, rxy, syz⟩, tzw⟩

@[simp]
theorem comp_right_id (r : Rel α β) : (r ∘ @Eq β) = r :=
  by 
    unfold comp 
    ext y 
    simp 

@[simp]
theorem comp_left_id (r : Rel α β) : (@Eq α ∘ r) = r :=
  by 
    unfold comp 
    ext x 
    simp 

theorem inv_id : inv (@Eq α) = @Eq α :=
  by 
    ext x y 
    split  <;> apply Eq.symm

theorem inv_comp (r : Rel α β) (s : Rel β γ) : inv (r ∘ s) = (inv s ∘ inv r) :=
  by 
    ext x z 
    simp [comp, inv, flip, And.comm]

/-- Image of a set under a relation -/
def image (s : Set α) : Set β :=
  { y | ∃ (x : _)(_ : x ∈ s), r x y }

theorem mem_image (y : β) (s : Set α) : y ∈ image r s ↔ ∃ (x : _)(_ : x ∈ s), r x y :=
  Iff.rfl

theorem image_subset : (· ⊆ ·⇒· ⊆ ·) r.image r.image :=
  fun s t h y ⟨x, xs, rxy⟩ => ⟨x, h xs, rxy⟩

theorem image_mono : Monotone r.image :=
  r.image_subset

theorem image_inter (s t : Set α) : r.image (s ∩ t) ⊆ r.image s ∩ r.image t :=
  r.image_mono.map_inf_le s t

theorem image_union (s t : Set α) : r.image (s ∪ t) = r.image s ∪ r.image t :=
  le_antisymmₓ (fun y ⟨x, xst, rxy⟩ => xst.elim (fun xs => Or.inl ⟨x, ⟨xs, rxy⟩⟩) fun xt => Or.inr ⟨x, ⟨xt, rxy⟩⟩)
    (r.image_mono.le_map_sup s t)

@[simp]
theorem image_id (s : Set α) : image (@Eq α) s = s :=
  by 
    ext x 
    simp [mem_image]

theorem image_comp (s : Rel β γ) (t : Set α) : image (r ∘ s) t = image s (image r t) :=
  by 
    ext z 
    simp only [mem_image, comp]
    split 
    ·
      rintro ⟨x, xt, y, rxy, syz⟩
      exact ⟨y, ⟨x, xt, rxy⟩, syz⟩
    rintro ⟨y, ⟨x, xt, rxy⟩, syz⟩
    exact ⟨x, xt, y, rxy, syz⟩

theorem image_univ : r.image Set.Univ = r.codom :=
  by 
    ext y 
    simp [mem_image, codom]

/-- Preimage of a set under a relation `r`. Same as the image of `s` under `r.inv` -/
def preimage (s : Set β) : Set α :=
  r.inv.image s

theorem mem_preimage (x : α) (s : Set β) : x ∈ r.preimage s ↔ ∃ (y : _)(_ : y ∈ s), r x y :=
  Iff.rfl

theorem preimage_def (s : Set β) : preimage r s = { x | ∃ (y : _)(_ : y ∈ s), r x y } :=
  Set.ext$ fun x => mem_preimage _ _ _

theorem preimage_mono {s t : Set β} (h : s ⊆ t) : r.preimage s ⊆ r.preimage t :=
  image_mono _ h

theorem preimage_inter (s t : Set β) : r.preimage (s ∩ t) ⊆ r.preimage s ∩ r.preimage t :=
  image_inter _ s t

theorem preimage_union (s t : Set β) : r.preimage (s ∪ t) = r.preimage s ∪ r.preimage t :=
  image_union _ s t

theorem preimage_id (s : Set α) : preimage (@Eq α) s = s :=
  by 
    simp only [preimage, inv_id, image_id]

theorem preimage_comp (s : Rel β γ) (t : Set γ) : preimage (r ∘ s) t = preimage r (preimage s t) :=
  by 
    simp only [preimage, inv_comp, image_comp]

theorem preimage_univ : r.preimage Set.Univ = r.dom :=
  by 
    rw [preimage, image_univ, codom_inv]

/-- Core of a set `s : set β` w.r.t `r : rel α β` is the set of `x : α` that are related *only*
to elements of `s`. Other generalization of `function.preimage`. -/
def core (s : Set β) :=
  { x | ∀ y, r x y → y ∈ s }

theorem mem_core (x : α) (s : Set β) : x ∈ r.core s ↔ ∀ y, r x y → y ∈ s :=
  Iff.rfl

theorem core_subset : (· ⊆ ·⇒· ⊆ ·) r.core r.core :=
  fun s t h x h' y rxy => h (h' y rxy)

theorem core_mono : Monotone r.core :=
  r.core_subset

theorem core_inter (s t : Set β) : r.core (s ∩ t) = r.core s ∩ r.core t :=
  Set.ext
    (by 
      simp [mem_core, imp_and_distrib, forall_and_distrib])

theorem core_union (s t : Set β) : r.core s ∪ r.core t ⊆ r.core (s ∪ t) :=
  r.core_mono.le_map_sup s t

@[simp]
theorem core_univ : r.core Set.Univ = Set.Univ :=
  Set.ext
    (by 
      simp [mem_core])

theorem core_id (s : Set α) : core (@Eq α) s = s :=
  by 
    simp [core]

theorem core_comp (s : Rel β γ) (t : Set γ) : core (r ∘ s) t = core r (core s t) :=
  by 
    ext x 
    simp [core, comp]
    split 
    ·
      exact fun h y rxy z => h z y rxy
    ·
      exact fun h z y rzy => h y rzy z

/-- Restrict the domain of a relation to a subtype. -/
def restrict_domain (s : Set α) : Rel { x // x ∈ s } β :=
  fun x y => r x.val y

theorem image_subset_iff (s : Set α) (t : Set β) : image r s ⊆ t ↔ s ⊆ core r t :=
  Iff.intro (fun h x xs y rxy => h ⟨x, xs, rxy⟩) fun h y ⟨x, xs, rxy⟩ => h xs y rxy

theorem image_core_gc : GaloisConnection r.image r.core :=
  image_subset_iff _

end Rel

namespace Function

/-- The graph of a function as a relation. -/
def graph (f : α → β) : Rel α β :=
  fun x y => f x = y

end Function

namespace Set

theorem image_eq (f : α → β) (s : Set α) : f '' s = (Function.Graph f).Image s :=
  by 
    simp [Set.Image, Function.Graph, Rel.Image]

theorem preimage_eq (f : α → β) (s : Set β) : f ⁻¹' s = (Function.Graph f).Preimage s :=
  by 
    simp [Set.Preimage, Function.Graph, Rel.Preimage, Rel.Inv, flip, Rel.Image]

theorem preimage_eq_core (f : α → β) (s : Set β) : f ⁻¹' s = (Function.Graph f).Core s :=
  by 
    simp [Set.Preimage, Function.Graph, Rel.Core]

end Set

