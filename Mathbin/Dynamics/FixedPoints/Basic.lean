import Mathbin.Data.Set.Function 
import Mathbin.Logic.Function.Iterate

/-!
# Fixed points of a self-map

In this file we define

* the predicate `is_fixed_pt f x := f x = x`;
* the set `fixed_points f` of fixed points of a self-map `f`.

We also prove some simple lemmas about `is_fixed_pt` and `∘`, `iterate`, and `semiconj`.

## Tags

fixed point
-/


universe u v

variable{α : Type u}{β : Type v}{f fa g : α → α}{x y : α}{fb : β → β}{m n k : ℕ}

namespace Function

/-- A point `x` is a fixed point of `f : α → α` if `f x = x`. -/
def is_fixed_pt (f : α → α) (x : α) :=
  f x = x

/-- Every point is a fixed point of `id`. -/
theorem is_fixed_pt_id (x : α) : is_fixed_pt id x :=
  (rfl : _)

namespace IsFixedPt

instance  [h : DecidableEq α] {f : α → α} {x : α} : Decidable (is_fixed_pt f x) :=
  h (f x) x

/-- If `x` is a fixed point of `f`, then `f x = x`. This is useful, e.g., for `rw` or `simp`.-/
protected theorem Eq (hf : is_fixed_pt f x) : f x = x :=
  hf

/-- If `x` is a fixed point of `f` and `g`, then it is a fixed point of `f ∘ g`. -/
protected theorem comp (hf : is_fixed_pt f x) (hg : is_fixed_pt g x) : is_fixed_pt (f ∘ g) x :=
  calc f (g x) = f x := congr_argₓ f hg 
    _ = x := hf
    

/-- If `x` is a fixed point of `f`, then it is a fixed point of `f^[n]`. -/
protected theorem iterate (hf : is_fixed_pt f x) (n : ℕ) : is_fixed_pt (f^[n]) x :=
  iterate_fixed hf n

/-- If `x` is a fixed point of `f ∘ g` and `g`, then it is a fixed point of `f`. -/
theorem left_of_comp (hfg : is_fixed_pt (f ∘ g) x) (hg : is_fixed_pt g x) : is_fixed_pt f x :=
  calc f x = f (g x) := congr_argₓ f hg.symm 
    _ = x := hfg
    

/-- If `x` is a fixed point of `f` and `g` is a left inverse of `f`, then `x` is a fixed
point of `g`. -/
theorem to_left_inverse (hf : is_fixed_pt f x) (h : left_inverse g f) : is_fixed_pt g x :=
  calc g x = g (f x) := congr_argₓ g hf.symm 
    _ = x := h x
    

/-- If `g` (semi)conjugates `fa` to `fb`, then it sends fixed points of `fa` to fixed points
of `fb`. -/
protected theorem map {x : α} (hx : is_fixed_pt fa x) {g : α → β} (h : semiconj g fa fb) : is_fixed_pt fb (g x) :=
  calc fb (g x) = g (fa x) := (h.eq x).symm 
    _ = g x := congr_argₓ g hx
    

protected theorem apply {x : α} (hx : is_fixed_pt f x) : is_fixed_pt f (f x) :=
  by 
    convert hx

end IsFixedPt

@[simp]
theorem injective.is_fixed_pt_apply_iff (hf : injective f) {x : α} : is_fixed_pt f (f x) ↔ is_fixed_pt f x :=
  ⟨fun h => hf h.eq, is_fixed_pt.apply⟩

/-- The set of fixed points of a map `f : α → α`. -/
def fixed_points (f : α → α) : Set α :=
  { x:α | is_fixed_pt f x }

instance fixed_points.decidable [DecidableEq α] (f : α → α) (x : α) : Decidable (x ∈ fixed_points f) :=
  is_fixed_pt.decidable

@[simp]
theorem mem_fixed_points : x ∈ fixed_points f ↔ is_fixed_pt f x :=
  Iff.rfl

theorem mem_fixed_points_iff {α : Type _} {f : α → α} {x : α} : x ∈ fixed_points f ↔ f x = x :=
  by 
    rfl

@[simp]
theorem fixed_points_id : fixed_points (@id α) = Set.Univ :=
  Set.ext$
    fun _ =>
      by 
        simpa using is_fixed_pt_id _

/-- If `g` semiconjugates `fa` to `fb`, then it sends fixed points of `fa` to fixed points
of `fb`. -/
theorem semiconj.maps_to_fixed_pts {g : α → β} (h : semiconj g fa fb) :
  Set.MapsTo g (fixed_points fa) (fixed_points fb) :=
  fun x hx => hx.map h

/-- Any two maps `f : α → β` and `g : β → α` are inverse of each other on the sets of fixed points
of `f ∘ g` and `g ∘ f`, respectively. -/
theorem inv_on_fixed_pts_comp (f : α → β) (g : β → α) : Set.InvOn f g (fixed_points$ f ∘ g) (fixed_points$ g ∘ f) :=
  ⟨fun x => id, fun x => id⟩

/-- Any map `f` sends fixed points of `g ∘ f` to fixed points of `f ∘ g`. -/
theorem maps_to_fixed_pts_comp (f : α → β) (g : β → α) : Set.MapsTo f (fixed_points$ g ∘ f) (fixed_points$ f ∘ g) :=
  fun x hx => hx.map$ fun x => rfl

/-- Given two maps `f : α → β` and `g : β → α`, `g` is a bijective map between the fixed points
of `f ∘ g` and the fixed points of `g ∘ f`. The inverse map is `f`, see `inv_on_fixed_pts_comp`. -/
theorem bij_on_fixed_pts_comp (f : α → β) (g : β → α) : Set.BijOn g (fixed_points$ f ∘ g) (fixed_points$ g ∘ f) :=
  (inv_on_fixed_pts_comp f g).BijOn (maps_to_fixed_pts_comp g f) (maps_to_fixed_pts_comp f g)

/-- If self-maps `f` and `g` commute, then they are inverse of each other on the set of fixed points
of `f ∘ g`. This is a particular case of `function.inv_on_fixed_pts_comp`. -/
theorem commute.inv_on_fixed_pts_comp (h : commute f g) : Set.InvOn f g (fixed_points$ f ∘ g) (fixed_points$ f ∘ g) :=
  by 
    simpa only [h.comp_eq] using inv_on_fixed_pts_comp f g

/-- If self-maps `f` and `g` commute, then `f` is bijective on the set of fixed points of `f ∘ g`.
This is a particular case of `function.bij_on_fixed_pts_comp`. -/
theorem commute.left_bij_on_fixed_pts_comp (h : commute f g) :
  Set.BijOn f (fixed_points$ f ∘ g) (fixed_points$ f ∘ g) :=
  by 
    simpa only [h.comp_eq] using bij_on_fixed_pts_comp g f

/-- If self-maps `f` and `g` commute, then `g` is bijective on the set of fixed points of `f ∘ g`.
This is a particular case of `function.bij_on_fixed_pts_comp`. -/
theorem commute.right_bij_on_fixed_pts_comp (h : commute f g) :
  Set.BijOn g (fixed_points$ f ∘ g) (fixed_points$ f ∘ g) :=
  by 
    simpa only [h.comp_eq] using bij_on_fixed_pts_comp f g

end Function

