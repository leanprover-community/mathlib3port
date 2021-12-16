import Mathbin.Data.Finset.Option 
import Mathbin.Data.Pfun

/-!
# Image of a `finset α` under a partially defined function

In this file we define `part.to_finset` and `finset.pimage`. We also prove some trivial lemmas about
these definitions.

## Tags

finite set, image, partial function
-/


variable {α β : Type _}

namespace Part

/-- Convert a `o : part α` with decidable `part.dom o` to `finset α`. -/
def to_finset (o : Part α) [Decidable o.dom] : Finset α :=
  o.to_option.to_finset

@[simp]
theorem mem_to_finset {o : Part α} [Decidable o.dom] {x : α} : x ∈ o.to_finset ↔ x ∈ o :=
  by 
    simp [to_finset]

@[simp]
theorem to_finset_none [Decidable (none : Part α).Dom] : none.toFinset = (∅ : Finset α) :=
  by 
    simp [to_finset]

@[simp]
theorem to_finset_some {a : α} [Decidable (some a).Dom] : (some a).toFinset = {a} :=
  by 
    simp [to_finset]

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    coe_to_finset
    ( o : Part α ) [ Decidable o.dom ] : ( o.to_finset : Set α ) = { x | x ∈ o }
    := Set.ext $ fun x => mem_to_finset

end Part

namespace Finset

variable [DecidableEq β] {f g : α →. β} [∀ x, Decidable (f x).Dom] [∀ x, Decidable (g x).Dom] {s t : Finset α} {b : β}

/-- Image of `s : finset α` under a partially defined function `f : α →. β`. -/
def pimage (f : α →. β) [∀ x, Decidable (f x).Dom] (s : Finset α) : Finset β :=
  s.bUnion fun x => (f x).toFinset

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a «expr ∈ » s)
@[simp]
theorem mem_pimage : b ∈ s.pimage f ↔ ∃ (a : _)(_ : a ∈ s), b ∈ f a :=
  by 
    simp [pimage]

@[simp, normCast]
theorem coe_pimage : (s.pimage f : Set β) = f.image s :=
  Set.ext$ fun x => mem_pimage

@[simp]
theorem pimage_some (s : Finset α) (f : α → β) [∀ x, Decidable (Part.some$ f x).Dom] :
  (s.pimage fun x => Part.some (f x)) = s.image f :=
  by 
    ext 
    simp [eq_comm]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » t)
-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  pimage_congr
  ( h₁ : s = t ) ( h₂ : ∀ x _ : x ∈ t , f x = g x ) : s.pimage f = t.pimage g
  := by subst s ext y simp ( config := { contextual := Bool.true._@._internal._hyg.0 } ) [ h₂ ]

/-- Rewrite `s.pimage f` in terms of `finset.filter`, `finset.attach`, and `finset.image`. -/
theorem pimage_eq_image_filter :
  s.pimage f = (filter (fun x => (f x).Dom) s).attach.Image fun x => (f x).get (mem_filter.1 x.coe_prop).2 :=
  by 
    ext x 
    simp [Part.mem_eq, And.exists, -exists_prop]

theorem pimage_union [DecidableEq α] : (s ∪ t).pimage f = s.pimage f ∪ t.pimage f :=
  coe_inj.1$
    by 
      simp only [coe_pimage, Pfun.image_union, coe_union]

@[simp]
theorem pimage_empty : pimage f ∅ = ∅ :=
  by 
    ext 
    simp 

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » f x)
theorem pimage_subset {t : Finset β} : s.pimage f ⊆ t ↔ ∀ x _ : x ∈ s y _ : y ∈ f x, y ∈ t :=
  by 
    simp [subset_iff, @forall_swap _ β]

@[mono]
theorem pimage_mono (h : s ⊆ t) : s.pimage f ⊆ t.pimage f :=
  pimage_subset.2$ fun x hx y hy => mem_pimage.2 ⟨x, h hx, hy⟩

theorem pimage_inter [DecidableEq α] : (s ∩ t).pimage f ⊆ s.pimage f ∩ t.pimage f :=
  by 
    simp only [←coe_subset, coe_pimage, coe_inter, Pfun.image_inter]

end Finset

