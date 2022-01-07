import Mathbin.Algebra.Category.CommRing.FilteredColimits
import Mathbin.AlgebraicGeometry.SheafedSpace
import Mathbin.Topology.Sheaves.Stalks
import Mathbin.Algebra.Category.CommRing.Colimits
import Mathbin.Algebra.Category.CommRing.Limits

/-!
# Ringed spaces

We introduce the category of ringed spaces, as an alias for `SheafedSpace CommRing`.

The facts collected in this file are typically stated for locally ringed spaces, but never actually
make use of the locality of stalks. See for instance https://stacks.math.columbia.edu/tag/01HZ.

-/


universe v

open CategoryTheory

open TopologicalSpace

open Opposite

open Top

open Top.Presheaf

namespace AlgebraicGeometry

/-- The type of Ringed spaces, as an abbreviation for `SheafedSpace CommRing`. -/
abbrev RingedSpace : Type _ :=
  SheafedSpace CommRingₓₓ

namespace RingedSpace

open SheafedSpace

variable (X : RingedSpace.{v})

/-- If the germ of a section `f` is a unit in the stalk at `x`, then `f` must be a unit on some small
neighborhood around `x`.
-/
theorem is_unit_res_of_is_unit_germ (U : opens X) (f : X.presheaf.obj (op U)) (x : U)
    (h : IsUnit (X.presheaf.germ x f)) : ∃ (V : opens X)(i : V ⟶ U)(hxV : x.1 ∈ V), IsUnit (X.presheaf.map i.op f) := by
  obtain ⟨g', heq⟩ := h.exists_right_inv
  obtain ⟨V, hxV, g, rfl⟩ := X.presheaf.germ_exist x.1 g'
  let W := U⊓V
  have hxW : x.1 ∈ W := ⟨x.2, hxV⟩
  erw [← X.presheaf.germ_res_apply (opens.inf_le_left U V) ⟨x.1, hxW⟩ f, ←
    X.presheaf.germ_res_apply (opens.inf_le_right U V) ⟨x.1, hxW⟩ g, ← RingHom.map_mul, ←
    RingHom.map_one (X.presheaf.germ (⟨x.1, hxW⟩ : W))] at heq
  obtain ⟨W', hxW', i₁, i₂, heq'⟩ := X.presheaf.germ_eq x.1 hxW hxW _ _ HEq
  use W', i₁ ≫ opens.inf_le_left U V, hxW'
  rw [RingHom.map_one, RingHom.map_mul, ← comp_apply, ← X.presheaf.map_comp, ← op_comp] at heq'
  exact is_unit_of_mul_eq_one _ _ heq'

/-- If a section `f` is a unit in each stalk, `f` must be a unit. -/
theorem is_unit_of_is_unit_germ (U : opens X) (f : X.presheaf.obj (op U)) (h : ∀ x : U, IsUnit (X.presheaf.germ x f)) :
    IsUnit f := by
  choose V iVU m h_unit using fun x : U => X.is_unit_res_of_is_unit_germ U f x (h x)
  have hcover : U ≤ supr V := by
    intro x hxU
    rw [opens.mem_coe, opens.mem_supr]
    exact ⟨⟨x, hxU⟩, m ⟨x, hxU⟩⟩
  choose g hg using fun x : U => IsUnit.exists_right_inv (h_unit x)
  obtain ⟨gl, gl_spec, -⟩ := X.sheaf.exists_unique_gluing' V U iVU hcover g _
  swap
  · intro x y
    apply section_ext X.sheaf (V x⊓V y)
    rintro ⟨z, hzVx, hzVy⟩
    rw [germ_res_apply, germ_res_apply]
    apply (IsUnit.mul_right_inj (h ⟨z, (iVU x).le hzVx⟩)).mp
    erw [← X.presheaf.germ_res_apply (iVU x) ⟨z, hzVx⟩ f, ← RingHom.map_mul,
      congr_argₓ (X.presheaf.germ (⟨z, hzVx⟩ : V x)) (hg x), germ_res_apply, ←
      X.presheaf.germ_res_apply (iVU y) ⟨z, hzVy⟩ f, ← RingHom.map_mul,
      congr_argₓ (X.presheaf.germ (⟨z, hzVy⟩ : V y)) (hg y), RingHom.map_one, RingHom.map_one]
    
  apply is_unit_of_mul_eq_one f gl
  apply X.sheaf.eq_of_locally_eq' V U iVU hcover
  intro i
  rw [RingHom.map_one, RingHom.map_mul, gl_spec]
  exact hg i

/-- The basic open of a section `f` is the set of all points `x`, such that the germ of `f` at
`x` is a unit.
-/
def basic_open {U : opens X} (f : X.presheaf.obj (op U)) : opens X where
  val := coeₓ '' { x : U | IsUnit (X.presheaf.germ x f) }
  property := by
    rw [is_open_iff_forall_mem_open]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨V, i, hxV, hf⟩ := X.is_unit_res_of_is_unit_germ U f x hx
    use V.1
    refine' ⟨_, V.2, hxV⟩
    intro y hy
    use (⟨y, i.le hy⟩ : U)
    rw [Set.mem_set_of_eq]
    constructor
    · convert RingHom.is_unit_map (X.presheaf.germ ⟨y, hy⟩) hf
      exact (X.presheaf.germ_res_apply i ⟨y, hy⟩ f).symm
      
    · rfl
      

@[simp]
theorem mem_basic_open {U : opens X} (f : X.presheaf.obj (op U)) (x : U) :
    ↑x ∈ X.basic_open f ↔ IsUnit (X.presheaf.germ x f) := by
  constructor
  · rintro ⟨x, hx, a⟩
    cases Subtype.eq a
    exact hx
    
  · intro h
    exact ⟨x, h, rfl⟩
    

@[simp]
theorem mem_top_basic_open (f : X.presheaf.obj (op ⊤)) (x : X) :
    x ∈ X.basic_open f ↔
      IsUnit
        (X.presheaf.germ
          ⟨x,
            show x ∈ (⊤ : opens X) by
              trivial⟩
          f) :=
  mem_basic_open X f ⟨x, _⟩

theorem basic_open_subset {U : opens X} (f : X.presheaf.obj (op U)) : X.basic_open f ⊆ U := by
  rintro _ ⟨x, hx, rfl⟩
  exact x.2

/-- The restriction of a section `f` to the basic open of `f` is a unit. -/
theorem is_unit_res_basic_open {U : opens X} (f : X.presheaf.obj (op U)) :
    IsUnit (X.presheaf.map (@hom_of_le (opens X) _ _ _ (X.basic_open_subset f)).op f) := by
  apply is_unit_of_is_unit_germ
  rintro ⟨_, ⟨x, hx, rfl⟩⟩
  convert hx
  rw [germ_res_apply]
  rfl

theorem basic_open_res {U V : opens Xᵒᵖ} (i : U ⟶ V) (f : X.presheaf.obj U) :
    @basic_open X (unop V) (X.presheaf.map i f) = unop V ∩ @basic_open X (unop U) f := by
  induction U using Opposite.rec
  induction V using Opposite.rec
  let g := i.unop
  have : i = g.op := rfl
  clear_value g
  subst this
  ext
  constructor
  · rintro ⟨x, hx : IsUnit _, rfl⟩
    rw [germ_res_apply] at hx
    exact ⟨x.2, g x, hx, rfl⟩
    
  · rintro ⟨hxV, x, hx, rfl⟩
    use ⟨x, hxV⟩
    constructor
    · change IsUnit _
      rw [germ_res_apply]
      exact hx
      
    · rfl
      
    

end RingedSpace

end AlgebraicGeometry

