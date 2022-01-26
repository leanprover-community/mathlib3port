import Mathbin.CategoryTheory.Elements
import Mathbin.CategoryTheory.IsConnected
import Mathbin.CategoryTheory.SingleObj
import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.GroupTheory.SemidirectProduct

/-!
# Actions as functors and as categories

From a multiplicative action M ↻ X, we can construct a functor from M to the category of
types, mapping the single object of M to X and an element `m : M` to map `X → X` given by
multiplication by `m`.
  This functor induces a category structure on X -- a special case of the category of elements.
A morphism `x ⟶ y` in this category is simply a scalar `m : M` such that `m • x = y`. In the case
where M is a group, this category is a groupoid -- the `action groupoid'.
-/


open MulAction SemidirectProduct

namespace CategoryTheory

universe u

variable (M : Type _) [Monoidₓ M] (X : Type u) [MulAction M X]

/-- A multiplicative action M ↻ X viewed as a functor mapping the single object of M to X
  and an element `m : M` to the map `X → X` given by multiplication by `m`. -/
@[simps]
def action_as_functor : single_obj M ⥤ Type u where
  obj := fun _ => X
  map := fun _ _ => · • ·
  map_id' := fun _ => funext <| MulAction.one_smul
  map_comp' := fun _ _ _ f g => funext fun x => (smul_smul g f x).symm

/-- A multiplicative action M ↻ X induces a category strucure on X, where a morphism
 from x to y is a scalar taking x to y. Due to implementation details, the object type
 of this category is not equal to X, but is in bijection with X. -/
def action_category :=
  (action_as_functor M X).Elements deriving category

namespace ActionCategory

/-- The projection from the action category to the monoid, mapping a morphism to its
  label. -/
def π : action_category M X ⥤ single_obj M :=
  category_of_elements.π _

@[simp]
theorem π_map (p q : action_category M X) (f : p ⟶ q) : (π M X).map f = f.val :=
  rfl

@[simp]
theorem π_obj (p : action_category M X) : (π M X).obj p = single_obj.star M :=
  Unit.ext

variable {M X}

/-- The canonical map `action_category M X → X`. It is given by `λ x, x.snd`, but
  has a more explicit type. -/
protected def back : action_category M X → X := fun x => x.snd

instance : CoeTₓ X (action_category M X) :=
  ⟨fun x => ⟨(), x⟩⟩

@[simp]
theorem coe_back (x : X) : (↑x : action_category M X).back = x :=
  rfl

@[simp]
theorem back_coe (x : action_category M X) : ↑x.back = x := by
  ext <;> rfl

variable (M X)

/-- An object of the action category given by M ↻ X corresponds to an element of X. -/
def obj_equiv : X ≃ action_category M X where
  toFun := coe
  invFun := fun x => x.back
  left_inv := coe_back
  right_inv := back_coe

theorem hom_as_subtype (p q : action_category M X) : (p ⟶ q) = { m : M // m • p.back = q.back } :=
  rfl

instance [Inhabited X] : Inhabited (action_category M X) :=
  ⟨show X from default⟩

instance [Nonempty X] : Nonempty (action_category M X) :=
  Nonempty.map (obj_equiv M X) inferInstance

variable {X} (x : X)

/-- The stabilizer of a point is isomorphic to the endomorphism monoid at the
  corresponding point. In fact they are definitionally equivalent. -/
def stabilizer_iso_End : stabilizer.submonoid M x ≃* End (↑x : action_category M X) :=
  MulEquiv.refl _

@[simp]
theorem stabilizer_iso_End_apply (f : stabilizer.submonoid M x) : (stabilizer_iso_End M x).toFun f = f :=
  rfl

@[simp]
theorem stabilizer_iso_End_symm_apply (f : End _) : (stabilizer_iso_End M x).invFun f = f :=
  rfl

variable {M X}

@[simp]
protected theorem id_val (x : action_category M X) : Subtype.val (𝟙 x) = 1 :=
  rfl

@[simp]
protected theorem comp_val {x y z : action_category M X} (f : x ⟶ y) (g : y ⟶ z) : (f ≫ g).val = g.val * f.val :=
  rfl

instance [is_pretransitive M X] [Nonempty X] : is_connected (action_category M X) :=
  zigzag_is_connected fun x y =>
    Relation.ReflTransGen.single <| Or.inl <| nonempty_subtype.mpr (show _ from exists_smul_eq M x.back y.back)

section Groupₓ

variable {G : Type _} [Groupₓ G] [MulAction G X]

noncomputable instance : groupoid (action_category G X) :=
  CategoryTheory.groupoidOfElements _

/-- Any subgroup of `G` is a vertex group in its action groupoid. -/
def End_mul_equiv_subgroup (H : Subgroup G) : End (obj_equiv G (G ⧸ H) ↑(1 : G)) ≃* H :=
  MulEquiv.trans (stabilizer_iso_End G ((1 : G) : G ⧸ H)).symm (MulEquiv.subgroupCongr <| stabilizer_quotient H)

/-- A target vertex `t` and a scalar `g` determine a morphism in the action groupoid. -/
def hom_of_pair (t : X) (g : G) : ↑(g⁻¹ • t) ⟶ (t : action_category G X) :=
  Subtype.mk g (smul_inv_smul g t)

@[simp]
theorem hom_of_pair.val (t : X) (g : G) : (hom_of_pair t g).val = g :=
  rfl

/-- Any morphism in the action groupoid is given by some pair. -/
protected def cases {P : ∀ ⦃a b : action_category G X⦄, (a ⟶ b) → Sort _} (hyp : ∀ t g, P (hom_of_pair t g)) ⦃a b⦄
    (f : a ⟶ b) : P f := by
  refine' cast _ (hyp b.back f.val)
  rcases a with ⟨⟨⟩, a : X⟩
  rcases b with ⟨⟨⟩, b : X⟩
  rcases f with ⟨g : G, h : g • a = b⟩
  cases inv_smul_eq_iff.mpr h.symm
  rfl

variable {H : Type _} [Groupₓ H]

/-- Given `G` acting on `X`, a functor from the corresponding action groupoid to a group `H`
    can be curried to a group homomorphism `G →* (X → H) ⋊ G`. -/
@[simps]
def curry (F : action_category G X ⥤ single_obj H) : G →* (X → H) ⋊[mulAutArrow] G :=
  have F_map_eq : ∀ {a b} {f : a ⟶ b}, F.map f = (F.map (hom_of_pair b.back f.val) : H) :=
    action_category.cases fun _ _ => rfl
  { toFun := fun g => ⟨fun b => F.map (hom_of_pair b g), g⟩,
    map_one' := by
      congr
      funext
      exact F_map_eq.symm.trans (F.map_id b),
    map_mul' := by
      intro g h
      congr
      funext
      exact F_map_eq.symm.trans (F.map_comp (hom_of_pair (g⁻¹ • b) h) (hom_of_pair b g)) }

/-- Given `G` acting on `X`, a group homomorphism `φ : G →* (X → H) ⋊ G` can be uncurried to
    a functor from the action groupoid to `H`, provided that `φ g = (_, g)` for all `g`. -/
@[simps]
def uncurry (F : G →* (X → H) ⋊[mulAutArrow] G) (sane : ∀ g, (F g).right = g) : action_category G X ⥤ single_obj H where
  obj := fun _ => ()
  map := fun a b f => (F f.val).left b.back
  map_id' := by
    intro x
    rw [action_category.id_val, F.map_one]
    rfl
  map_comp' := by
    intro x y z f g
    revert y z g
    refine' action_category.cases _
    simp [single_obj.comp_as_mul, sane]

end Groupₓ

end ActionCategory

end CategoryTheory

