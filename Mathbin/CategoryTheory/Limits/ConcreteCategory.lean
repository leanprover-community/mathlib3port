import Mathbin.CategoryTheory.Limits.Preserves.Basic 
import Mathbin.CategoryTheory.Limits.Types 
import Mathbin.CategoryTheory.Limits.Shapes.WidePullbacks 
import Mathbin.CategoryTheory.Limits.Shapes.Multiequalizer 
import Mathbin.Tactic.Elementwise

/-!
# Facts about (co)limits of functors into concrete categories
-/


universe w v u

open CategoryTheory

namespace CategoryTheory.Limits

attribute [elementwise] cone.w limit.lift_π limit.w cocone.w colimit.ι_desc colimit.w

attribute [local instance] concrete_category.has_coe_to_fun concrete_category.has_coe_to_sort

section Limits

variable{C :
    Type
      u}[category.{v} C][concrete_category.{v} C]{J : Type v}[small_category J](F : J ⥤ C)[preserves_limit F (forget C)]

theorem concrete.to_product_injective_of_is_limit {D : cone F} (hD : is_limit D) :
  Function.Injective fun x : D.X j : J => D.π.app j x :=
  by 
    let E := (forget C).mapCone D 
    let hE : is_limit E := is_limit_of_preserves _ hD 
    let G := types.limit_cone (F ⋙ forget C)
    let hG := types.limit_cone_is_limit (F ⋙ forget C)
    let T : E.X ≅ G.X := hE.cone_point_unique_up_to_iso hG 
    change Function.Injective (T.hom ≫ fun x j => G.π.app j x)
    have h : Function.Injective T.hom
    ·
      intro a b h 
      suffices  : T.inv (T.hom a) = T.inv (T.hom b)
      ·
        simpa 
      rw [h]
    suffices  : Function.Injective fun x : G.X j => G.π.app j x
    ·
      exact this.comp h 
    apply Subtype.ext

theorem concrete.is_limit_ext {D : cone F} (hD : is_limit D) (x y : D.X) : (∀ j, D.π.app j x = D.π.app j y) → x = y :=
  fun h => concrete.to_product_injective_of_is_limit _ hD (funext h)

theorem concrete.limit_ext [has_limit F] (x y : limit F) : (∀ j, limit.π F j x = limit.π F j y) → x = y :=
  concrete.is_limit_ext F (limit.is_limit _) _ _

section WidePullback

open WidePullback

open WidePullbackShape

theorem concrete.wide_pullback_ext {B : C} {ι : Type _} {X : ι → C} (f : ∀ j : ι, X j ⟶ B) [has_wide_pullback B X f]
  [preserves_limit (wide_cospan B X f) (forget C)] (x y : wide_pullback B X f) (h₀ : base f x = base f y)
  (h : ∀ j, π f j x = π f j y) : x = y :=
  by 
    apply concrete.limit_ext 
    rintro (_ | j)
    ·
      exact h₀
    ·
      apply h

theorem concrete.wide_pullback_ext' {B : C} {ι : Type _} [Nonempty ι] {X : ι → C} (f : ∀ j : ι, X j ⟶ B)
  [has_wide_pullback B X f] [preserves_limit (wide_cospan B X f) (forget C)] (x y : wide_pullback B X f)
  (h : ∀ j, π f j x = π f j y) : x = y :=
  by 
    apply concrete.wide_pullback_ext _ _ _ _ h 
    inhabit ι 
    simp only [←π_arrow f (arbitraryₓ _), comp_apply, h]

end WidePullback

section Multiequalizer

theorem concrete.multiequalizer_ext {I : multicospan_index C} [has_multiequalizer I]
  [preserves_limit I.multicospan (forget C)] (x y : multiequalizer I)
  (h : ∀ t : I.L, multiequalizer.ι I t x = multiequalizer.ι I t y) : x = y :=
  by 
    apply concrete.limit_ext 
    rintro (a | b)
    ·
      apply h
    ·
      rw [←limit.w I.multicospan (walking_multicospan.hom.fst b), comp_apply, comp_apply, h]

/-- An auxiliary equivalence to be used in `multiequalizer_equiv` below.-/
def concrete.multiequalizer_equiv_aux (I : multicospan_index C) :
  (I.multicospan ⋙ forget C).sections ≃ { x : ∀ i : I.L, I.left i // ∀ i : I.R, I.fst i (x _) = I.snd i (x _) } :=
  { toFun :=
      fun x =>
        ⟨fun i => x.1 (walking_multicospan.left _),
          fun i =>
            by 
              have a := x.2 (walking_multicospan.hom.fst i)
              have b := x.2 (walking_multicospan.hom.snd i)
              rw [←b] at a 
              exact a⟩,
    invFun :=
      fun x =>
        { val :=
            fun j =>
              match j with 
              | walking_multicospan.left a => x.1 _
              | walking_multicospan.right b => I.fst b (x.1 _),
          property :=
            by 
              rintro (a | b) (a' | b') (f | f | f)
              ·
                change (I.multicospan.map (𝟙 _)) _ = _ 
                simp 
              ·
                rfl
              ·
                dsimp 
                erw [←x.2 b']
                rfl
              ·
                change (I.multicospan.map (𝟙 _)) _ = _ 
                simp  },
    left_inv :=
      by 
        intro x 
        ext (a | b)
        ·
          rfl
        ·
          change _ = x.val _ 
          rw [←x.2 (walking_multicospan.hom.fst b)]
          rfl,
    right_inv :=
      by 
        intro x 
        ext i 
        rfl }

/-- The equivalence between the noncomputable multiequalizer and
and the concrete multiequalizer. -/
noncomputable def concrete.multiequalizer_equiv (I : multicospan_index C) [has_multiequalizer I]
  [preserves_limit I.multicospan (forget C)] :
  (multiequalizer I : C) ≃ { x : ∀ i : I.L, I.left i // ∀ i : I.R, I.fst i (x _) = I.snd i (x _) } :=
  let h1 := limit.is_limit I.multicospan 
  let h2 := is_limit_of_preserves (forget C) h1 
  let E := h2.cone_point_unique_up_to_iso (types.limit_cone_is_limit _)
  Equiv.trans E.to_equiv (concrete.multiequalizer_equiv_aux I)

@[simp]
theorem concrete.multiequalizer_equiv_apply (I : multicospan_index C) [has_multiequalizer I]
  [preserves_limit I.multicospan (forget C)] (x : multiequalizer I) (i : I.L) :
  ((concrete.multiequalizer_equiv I) x : ∀ i : I.L, I.left i) i = multiequalizer.ι I i x :=
  rfl

end Multiequalizer

end Limits

section Colimits

variable{C :
    Type
      u}[category.{v}
      C][concrete_category.{v} C]{J : Type v}[small_category J](F : J ⥤ C)[preserves_colimit F (forget C)]

theorem concrete.from_union_surjective_of_is_colimit {D : cocone F} (hD : is_colimit D) :
  let ff : (Σj : J, F.obj j) → D.X := fun a => D.ι.app a.1 a.2
  Function.Surjective ff :=
  by 
    intro ff 
    let E := (forget C).mapCocone D 
    let hE : is_colimit E := is_colimit_of_preserves _ hD 
    let G := types.colimit_cocone (F ⋙ forget C)
    let hG := types.colimit_cocone_is_colimit (F ⋙ forget C)
    let T : E ≅ G := hE.unique_up_to_iso hG 
    let TX : E.X ≅ G.X := (cocones.forget _).mapIso T 
    suffices  : Function.Surjective (TX.hom ∘ ff)
    ·
      intro a 
      obtain ⟨b, hb⟩ := this (TX.hom a)
      refine' ⟨b, _⟩
      applyFun TX.inv  at hb 
      change (TX.hom ≫ TX.inv) (ff b) = (TX.hom ≫ TX.inv) _ at hb 
      simpa only [TX.hom_inv_id] using hb 
    have  : TX.hom ∘ ff = fun a => G.ι.app a.1 a.2
    ·
      ext a 
      change (E.ι.app a.1 ≫ hE.desc G) a.2 = _ 
      rw [hE.fac]
    rw [this]
    rintro ⟨⟨j, a⟩⟩
    exact ⟨⟨j, a⟩, rfl⟩

theorem concrete.is_colimit_exists_rep {D : cocone F} (hD : is_colimit D) (x : D.X) :
  ∃ (j : J)(y : F.obj j), D.ι.app j y = x :=
  by 
    obtain ⟨a, rfl⟩ := concrete.from_union_surjective_of_is_colimit F hD x 
    exact ⟨a.1, a.2, rfl⟩

theorem concrete.colimit_exists_rep [has_colimit F] (x : colimit F) : ∃ (j : J)(y : F.obj j), colimit.ι F j y = x :=
  concrete.is_colimit_exists_rep F (colimit.is_colimit _) x

theorem concrete.is_colimit_rep_eq_of_exists {D : cocone F} {i j : J} (hD : is_colimit D) (x : F.obj i) (y : F.obj j)
  (h : ∃ (k : _)(f : i ⟶ k)(g : j ⟶ k), F.map f x = F.map g y) : D.ι.app i x = D.ι.app j y :=
  by 
    let E := (forget C).mapCocone D 
    let hE : is_colimit E := is_colimit_of_preserves _ hD 
    let G := types.colimit_cocone (F ⋙ forget C)
    let hG := types.colimit_cocone_is_colimit (F ⋙ forget C)
    let T : E ≅ G := hE.unique_up_to_iso hG 
    let TX : E.X ≅ G.X := (cocones.forget _).mapIso T 
    applyFun TX.hom 
    swap
    ·
      suffices  : Function.Bijective TX.hom
      ·
        exact this.1
      rw [←is_iso_iff_bijective]
      apply is_iso.of_iso 
    change (E.ι.app i ≫ TX.hom) x = (E.ι.app j ≫ TX.hom) y 
    erw [T.hom.w, T.hom.w]
    obtain ⟨k, f, g, h⟩ := h 
    have  : G.ι.app i x = (G.ι.app k (F.map f x) : G.X) := Quot.sound ⟨f, rfl⟩
    rw [this, h]
    symm 
    exact Quot.sound ⟨g, rfl⟩

theorem concrete.colimit_rep_eq_of_exists [has_colimit F] {i j : J} (x : F.obj i) (y : F.obj j)
  (h : ∃ (k : _)(f : i ⟶ k)(g : j ⟶ k), F.map f x = F.map g y) : colimit.ι F i x = colimit.ι F j y :=
  concrete.is_colimit_rep_eq_of_exists F (colimit.is_colimit _) x y h

section FilteredColimits

variable[is_filtered J]

theorem concrete.is_colimit_exists_of_rep_eq {D : cocone F} {i j : J} (hD : is_colimit D) (x : F.obj i) (y : F.obj j)
  (h : D.ι.app _ x = D.ι.app _ y) : ∃ (k : _)(f : i ⟶ k)(g : j ⟶ k), F.map f x = F.map g y :=
  by 
    let E := (forget C).mapCocone D 
    let hE : is_colimit E := is_colimit_of_preserves _ hD 
    let G := types.colimit_cocone (F ⋙ forget C)
    let hG := types.colimit_cocone_is_colimit (F ⋙ forget C)
    let T : E ≅ G := hE.unique_up_to_iso hG 
    let TX : E.X ≅ G.X := (cocones.forget _).mapIso T 
    applyFun TX.hom  at h 
    change (E.ι.app i ≫ TX.hom) x = (E.ι.app j ≫ TX.hom) y at h 
    erw [T.hom.w, T.hom.w] at h 
    replace h := Quot.exact _ h 
    suffices  :
      ∀ a b : Σj, F.obj j h : EqvGen (limits.types.quot.rel (F ⋙ forget C)) a b,
        ∃ (k : _)(f : a.1 ⟶ k)(g : b.1 ⟶ k), F.map f a.2 = F.map g b.2
    ·
      exact this ⟨i, x⟩ ⟨j, y⟩ h 
    intro a b h 
    induction h 
    case eqv_gen.rel x y hh => 
      obtain ⟨e, he⟩ := hh 
      use y.1, e, 𝟙 _ 
      simpa using he.symm 
    case eqv_gen.refl x => 
      use x.1, 𝟙 _, 𝟙 _, rfl 
    case eqv_gen.symm x y _ hh => 
      obtain ⟨k, f, g, hh⟩ := hh 
      use k, g, f, hh.symm 
    case eqv_gen.trans x y z _ _ hh1 hh2 => 
      obtain ⟨k1, f1, g1, h1⟩ := hh1 
      obtain ⟨k2, f2, g2, h2⟩ := hh2 
      let k0 : J := is_filtered.max k1 k2 
      let e1 : k1 ⟶ k0 := is_filtered.left_to_max _ _ 
      let e2 : k2 ⟶ k0 := is_filtered.right_to_max _ _ 
      let k : J := is_filtered.coeq (g1 ≫ e1) (f2 ≫ e2)
      let e : k0 ⟶ k := is_filtered.coeq_hom _ _ 
      use k, f1 ≫ e1 ≫ e, g2 ≫ e2 ≫ e 
      simp only [F.map_comp, comp_apply, h1, ←h2]
      simp only [←comp_apply, ←F.map_comp]
      rw [is_filtered.coeq_condition]

theorem concrete.is_colimit_rep_eq_iff_exists {D : cocone F} {i j : J} (hD : is_colimit D) (x : F.obj i) (y : F.obj j) :
  D.ι.app i x = D.ι.app j y ↔ ∃ (k : _)(f : i ⟶ k)(g : j ⟶ k), F.map f x = F.map g y :=
  ⟨concrete.is_colimit_exists_of_rep_eq _ hD _ _, concrete.is_colimit_rep_eq_of_exists _ hD _ _⟩

theorem concrete.colimit_exists_of_rep_eq [has_colimit F] {i j : J} (x : F.obj i) (y : F.obj j)
  (h : colimit.ι F _ x = colimit.ι F _ y) : ∃ (k : _)(f : i ⟶ k)(g : j ⟶ k), F.map f x = F.map g y :=
  concrete.is_colimit_exists_of_rep_eq F (colimit.is_colimit _) x y h

theorem concrete.colimit_rep_eq_iff_exists [has_colimit F] {i j : J} (x : F.obj i) (y : F.obj j) :
  colimit.ι F i x = colimit.ι F j y ↔ ∃ (k : _)(f : i ⟶ k)(g : j ⟶ k), F.map f x = F.map g y :=
  ⟨concrete.colimit_exists_of_rep_eq _ _ _, concrete.colimit_rep_eq_of_exists _ _ _⟩

end FilteredColimits

section WidePushout

open WidePushout

open WidePushoutShape

theorem concrete.wide_pushout_exists_rep {B : C} {α : Type _} {X : α → C} (f : ∀ j : α, B ⟶ X j)
  [has_wide_pushout B X f] [preserves_colimit (wide_span B X f) (forget C)] (x : wide_pushout B X f) :
  (∃ y : B, head f y = x) ∨ ∃ (i : α)(y : X i), ι f i y = x :=
  by 
    obtain ⟨_ | j, y, rfl⟩ := concrete.colimit_exists_rep _ x
    ·
      use y
    ·
      right 
      use j, y

theorem concrete.wide_pushout_exists_rep' {B : C} {α : Type _} [Nonempty α] {X : α → C} (f : ∀ j : α, B ⟶ X j)
  [has_wide_pushout B X f] [preserves_colimit (wide_span B X f) (forget C)] (x : wide_pushout B X f) :
  ∃ (i : α)(y : X i), ι f i y = x :=
  by 
    rcases concrete.wide_pushout_exists_rep f x with (⟨y, rfl⟩ | ⟨i, y, rfl⟩)
    ·
      inhabit α 
      use arbitraryₓ _, f _ y 
      simp only [←arrow_ι _ (arbitraryₓ α), comp_apply]
    ·
      use i, y

end WidePushout

end Colimits

end CategoryTheory.Limits

