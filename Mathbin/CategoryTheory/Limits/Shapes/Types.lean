import Mathbin.CategoryTheory.Limits.Types 
import Mathbin.CategoryTheory.Limits.Shapes.Products 
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts 
import Mathbin.CategoryTheory.Limits.Shapes.Terminal

/-!
# Special shapes for limits in `Type`.

The general shape (co)limits defined in `category_theory.limits.types`
are intended for use through the limits API,
and the actual implementation should mostly be considered "sealed".

In this file, we provide definitions of the "standard" special shapes of limits in `Type`,
giving the expected definitional implementation:
* the terminal object is `punit`
* the binary product of `X` and `Y` is `X × Y`
* the product of a family `f : J → Type` is `Π j, f j`
* the coproduct of a family `f : J → Type` is `Σ j, f j`
* the binary coproduct of `X` and `Y` is the sum type `X ⊕ Y`
* the equalizer of a pair of maps `(g, h)` is the subtype `{x : Y // g x = h x}`
* the coequalizer of a pair of maps `(f, g)` is the quotient of `Y` by `∀ x : Y, f x ~ g x`
* the pullback of `f : X ⟶ Z` and `g : Y ⟶ Z` is the subtype `{ p : X × Y // f p.1 = g p.2 }`
  of the product

Because these are not intended for use with the `has_limit` API,
we instead construct terms of `limit_data`.

As an example, when setting up the monoidal category structure on `Type`
we use the `types_has_terminal` and `types_has_binary_products` instances.
-/


universe u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Limits.Types

/-- A restatement of `types.lift_π_apply` that uses `pi.π` and `pi.lift`. -/
@[simp]
theorem pi_lift_π_apply {β : Type u} (f : β → Type u) {P : Type u} (s : ∀ b, P ⟶ f b) (b : β) (x : P) :
  (pi.π f b : (∏ f) → f b) (@pi.lift β _ _ f _ P s x) = s b x :=
  congr_funₓ (limit.lift_π (fan.mk P s) b) x

/-- A restatement of `types.map_π_apply` that uses `pi.π` and `pi.map`. -/
@[simp]
theorem pi_map_π_apply {β : Type u} {f g : β → Type u} (α : ∀ j, f j ⟶ g j) (b : β) x :
  (pi.π g b : (∏ g) → g b) (pi.map α x) = α b ((pi.π f b : (∏ f) → f b) x) :=
  limit.map_π_apply _ _ _

/-- The category of types has `punit` as a terminal object. -/
def terminal_limit_cone : limits.limit_cone (functor.empty (Type u)) :=
  { Cone :=
      { x := PUnit,
        π :=
          by 
            tidy },
    IsLimit :=
      by 
        tidy }

/-- The category of types has `pempty` as an initial object. -/
def initial_limit_cone : limits.colimit_cocone (functor.empty (Type u)) :=
  { Cocone :=
      { x := Pempty,
        ι :=
          by 
            tidy },
    IsColimit :=
      by 
        tidy }

open CategoryTheory.Limits.WalkingPair

/-- The product type `X × Y` forms a cone for the binary product of `X` and `Y`. -/
@[simps x]
def binary_product_cone (X Y : Type u) : binary_fan X Y :=
  binary_fan.mk Prod.fst Prod.snd

@[simp]
theorem binary_product_cone_fst (X Y : Type u) : (binary_product_cone X Y).fst = Prod.fst :=
  rfl

@[simp]
theorem binary_product_cone_snd (X Y : Type u) : (binary_product_cone X Y).snd = Prod.snd :=
  rfl

/-- The product type `X × Y` is a binary product for `X` and `Y`. -/
@[simps]
def binary_product_limit (X Y : Type u) : is_limit (binary_product_cone X Y) :=
  { lift := fun s : binary_fan X Y x => (s.fst x, s.snd x), fac' := fun s j => walking_pair.cases_on j rfl rfl,
    uniq' := fun s m w => funext$ fun x => Prod.extₓ (congr_funₓ (w left) x) (congr_funₓ (w right) x) }

/--
The category of types has `X × Y`, the usual cartesian product,
as the binary product of `X` and `Y`.
-/
@[simps]
def binary_product_limit_cone (X Y : Type u) : limits.limit_cone (pair X Y) :=
  ⟨_, binary_product_limit X Y⟩

/-- The functor which sends `X, Y` to the product type `X × Y`. -/
@[simps (config := { typeMd := reducible })]
def binary_product_functor : Type u ⥤ Type u ⥤ Type u :=
  { obj :=
      fun X =>
        { obj := fun Y => X × Y,
          map := fun Y₁ Y₂ f => (binary_product_limit X Y₂).lift (binary_fan.mk Prod.fst (Prod.snd ≫ f)) },
    map := fun X₁ X₂ f => { app := fun Y => (binary_product_limit X₂ Y).lift (binary_fan.mk (Prod.fst ≫ f) Prod.snd) } }

/--
The product functor given by the instance `has_binary_products (Type u)` is isomorphic to the
explicit binary product functor given by the product type.
-/
noncomputable def binary_product_iso_prod : binary_product_functor ≅ (prod.functor : Type u ⥤ _) :=
  by 
    apply nat_iso.of_components (fun X => _) _
    ·
      apply nat_iso.of_components (fun Y => _) _
      ·
        exact ((limit.is_limit _).conePointUniqueUpToIso (binary_product_limit X Y)).symm
      ·
        intro Y₁ Y₂ f 
        ext1 <;> simp 
    ·
      intro X₁ X₂ g 
      ext : 3 <;> simp 

/-- The sum type `X ⊕ Y` forms a cocone for the binary coproduct of `X` and `Y`. -/
@[simps]
def binary_coproduct_cocone (X Y : Type u) : cocone (pair X Y) :=
  binary_cofan.mk Sum.inl Sum.inr

/-- The sum type `X ⊕ Y` is a binary coproduct for `X` and `Y`. -/
@[simps]
def binary_coproduct_colimit (X Y : Type u) : is_colimit (binary_coproduct_cocone X Y) :=
  { desc := fun s : binary_cofan X Y => Sum.elim s.inl s.inr, fac' := fun s j => walking_pair.cases_on j rfl rfl,
    uniq' := fun s m w => funext$ fun x => Sum.casesOn x (congr_funₓ (w left)) (congr_funₓ (w right)) }

/--
The category of types has `X ⊕ Y`,
as the binary coproduct of `X` and `Y`.
-/
def binary_coproduct_colimit_cocone (X Y : Type u) : limits.colimit_cocone (pair X Y) :=
  ⟨_, binary_coproduct_colimit X Y⟩

/--
The category of types has `Π j, f j` as the product of a type family `f : J → Type`.
-/
def product_limit_cone {J : Type u} (F : J → Type u) : limits.limit_cone (discrete.functor F) :=
  { Cone := { x := ∀ j, F j, π := { app := fun j f => f j } },
    IsLimit :=
      { lift := fun s x j => s.π.app j x,
        uniq' := fun s m w => funext$ fun x => funext$ fun j => (congr_funₓ (w j) x : _) } }

-- error in CategoryTheory.Limits.Shapes.Types: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The category of types has `Σ j, f j` as the coproduct of a type family `f : J → Type`.
-/ def coproduct_colimit_cocone {J : Type u} (F : J → Type u) : limits.colimit_cocone (discrete.functor F) :=
{ cocone := { X := «exprΣ , »((j), F j), ι := { app := λ j x, ⟨j, x⟩ } },
  is_colimit := { desc := λ s x, s.ι.app x.1 x.2,
    uniq' := λ s m w, begin
      ext [] ["⟨", ident j, ",", ident x, "⟩"] [],
      have [] [] [":=", expr congr_fun (w j) x],
      exact [expr this]
    end } }

section Fork

variable {X Y Z : Type u} (f : X ⟶ Y) {g h : Y ⟶ Z} (w : f ≫ g = f ≫ h)

/--
Show the given fork in `Type u` is an equalizer given that any element in the "difference kernel"
comes from `X`.
The converse of `unique_of_type_equalizer`.
-/
noncomputable def type_equalizer_of_unique (t : ∀ y : Y, g y = h y → ∃!x : X, f x = y) : is_limit (fork.of_ι _ w) :=
  fork.is_limit.mk' _$
    fun s =>
      by 
        refine' ⟨fun i => _, _, _⟩
        ·
          apply Classical.some (t (s.ι i) _)
          apply congr_funₓ s.condition i
        ·
          ext i 
          apply (Classical.some_spec (t (s.ι i) _)).1
        ·
          intro m hm 
          ext i 
          apply (Classical.some_spec (t (s.ι i) _)).2
          apply congr_funₓ hm i

-- error in CategoryTheory.Limits.Shapes.Types: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The converse of `type_equalizer_of_unique`. -/
theorem unique_of_type_equalizer
(t : is_limit (fork.of_ι _ w))
(y : Y)
(hy : «expr = »(g y, h y)) : «expr∃! , »((x : X), «expr = »(f x, y)) :=
begin
  let [ident y'] [":", expr «expr ⟶ »(punit, Y)] [":=", expr λ _, y],
  have [ident hy'] [":", expr «expr = »(«expr ≫ »(y', g), «expr ≫ »(y', h))] [":=", expr funext (λ _, hy)],
  refine [expr ⟨(fork.is_limit.lift' t _ hy').1 ⟨⟩, congr_fun (fork.is_limit.lift' t y' _).2 ⟨⟩, _⟩],
  intros [ident x', ident hx'],
  suffices [] [":", expr «expr = »(λ _ : punit, x', (fork.is_limit.lift' t y' hy').1)],
  rw ["<-", expr this] [],
  apply [expr fork.is_limit.hom_ext t],
  ext [] ["⟨", "⟩"] [],
  apply [expr hx'.trans (congr_fun (fork.is_limit.lift' t _ hy').2 ⟨⟩).symm]
end

theorem type_equalizer_iff_unique : Nonempty (is_limit (fork.of_ι _ w)) ↔ ∀ y : Y, g y = h y → ∃!x : X, f x = y :=
  ⟨fun i => unique_of_type_equalizer _ _ (Classical.choice i), fun k => ⟨type_equalizer_of_unique f w k⟩⟩

/-- Show that the subtype `{x : Y // g x = h x}` is an equalizer for the pair `(g,h)`. -/
def equalizer_limit : limits.limit_cone (parallel_pair g h) :=
  { Cone := fork.of_ι (Subtype.val : { x : Y // g x = h x } → Y) (funext Subtype.prop),
    IsLimit :=
      fork.is_limit.mk' _$
        fun s =>
          ⟨fun i =>
              ⟨s.ι i,
                by 
                  apply congr_funₓ s.condition i⟩,
            rfl, fun m hm => funext$ fun x => Subtype.ext (congr_funₓ hm x)⟩ }

end Fork

section Cofork

variable {X Y Z : Type u} (f g : X ⟶ Y)

/-- (Implementation) The relation to be quotiented to obtain the coequalizer. -/
inductive coequalizer_rel : Y → Y → Prop
  | rel (x : X) : coequalizer_rel (f x) (g x)

/--
Show that the quotient by the relation generated by `f(x) ~ g(x)`
is a coequalizer for the pair `(f, g)`.
-/
def coequalizer_colimit : limits.colimit_cocone (parallel_pair f g) :=
  { Cocone := cofork.of_π (Quot.mk (coequalizer_rel f g)) (funext fun x => Quot.sound (coequalizer_rel.rel x)),
    IsColimit :=
      cofork.is_colimit.mk' _$
        fun s =>
          ⟨Quot.lift s.π
              fun a b h : coequalizer_rel f g a b =>
                by 
                  cases h 
                  exact congr_funₓ s.condition h_1,
            rfl, fun m hm => funext$ fun x => Quot.induction_on x (congr_funₓ hm : _)⟩ }

end Cofork

section Pullback

open CategoryTheory.Limits.WalkingPair

open CategoryTheory.Limits.WalkingCospan

open CategoryTheory.Limits.WalkingCospan.Hom

variable {W X Y Z : Type u}

variable (f : X ⟶ Z) (g : Y ⟶ Z)

/--
The usual explicit pullback in the category of types, as a subtype of the product.
The full `limit_cone` data is bundled as `pullback_limit_cone f g`.
-/
@[nolint has_inhabited_instance]
abbrev pullback_obj : Type u :=
  { p : X × Y // f p.1 = g p.2 }

example (p : pullback_obj f g) : X × Y :=
  p

/--
The explicit pullback cone on `pullback_obj f g`.
This is bundled with the `is_limit` data as `pullback_limit_cone f g`.
-/
abbrev pullback_cone : limits.pullback_cone f g :=
  pullback_cone.mk (fun p : pullback_obj f g => p.1.1) (fun p => p.1.2) (funext fun p => p.2)

/--
The explicit pullback in the category of types, bundled up as a `limit_cone`
for given `f` and `g`.
-/
@[simps]
def pullback_limit_cone (f : X ⟶ Z) (g : Y ⟶ Z) : limits.limit_cone (cospan f g) :=
  { Cone := pullback_cone f g,
    IsLimit :=
      pullback_cone.is_limit_aux _ (fun s x => ⟨⟨s.fst x, s.snd x⟩, congr_funₓ s.condition x⟩)
        (by 
          tidy)
        (by 
          tidy)
        fun s m w =>
          funext$
            fun x =>
              Subtype.ext$ Prod.extₓ (congr_funₓ (w walking_cospan.left) x) (congr_funₓ (w walking_cospan.right) x) }

/--
The pullback cone given by the instance `has_pullbacks (Type u)` is isomorphic to the
explicit pullback cone given by `pullback_limit_cone`.
-/
noncomputable def pullback_cone_iso_pullback : limit.cone (cospan f g) ≅ pullback_cone f g :=
  (limit.is_limit _).uniqueUpToIso (pullback_limit_cone f g).IsLimit

/--
The pullback given by the instance `has_pullbacks (Type u)` is isomorphic to the
explicit pullback object given by `pullback_limit_obj`.
-/
noncomputable def pullback_iso_pullback : pullback f g ≅ pullback_obj f g :=
  (cones.forget _).mapIso$ pullback_cone_iso_pullback f g

@[simp]
theorem pullback_iso_pullback_hom_fst (p : pullback f g) :
  ((pullback_iso_pullback f g).Hom p : X × Y).fst = (pullback.fst : _ ⟶ X) p :=
  congr_funₓ ((pullback_cone_iso_pullback f g).Hom.w left) p

@[simp]
theorem pullback_iso_pullback_hom_snd (p : pullback f g) :
  ((pullback_iso_pullback f g).Hom p : X × Y).snd = (pullback.snd : _ ⟶ Y) p :=
  congr_funₓ ((pullback_cone_iso_pullback f g).Hom.w right) p

@[simp]
theorem pullback_iso_pullback_inv_fst : (pullback_iso_pullback f g).inv ≫ pullback.fst = fun p => (p : X × Y).fst :=
  (pullback_cone_iso_pullback f g).inv.w left

@[simp]
theorem pullback_iso_pullback_inv_snd : (pullback_iso_pullback f g).inv ≫ pullback.snd = fun p => (p : X × Y).snd :=
  (pullback_cone_iso_pullback f g).inv.w right

end Pullback

end CategoryTheory.Limits.Types

