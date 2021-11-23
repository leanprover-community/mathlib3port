import Mathbin.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts 
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Products 
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts 
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts 
import Mathbin.CategoryTheory.Pempty 
import Mathbin.Data.Equiv.Fin

/-!
# Constructing finite products from binary products and terminal.

If a category has binary products and a terminal object then it has finite products.
If a functor preserves binary products and the terminal object then it preserves finite products.

# TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/


universe v u u'

noncomputable theory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

variable{J : Type v}[small_category J]

variable{C : Type u}[category.{v} C]

variable{D : Type u'}[category.{v} D]

/--
Given `n+1` objects of `C`, a fan for the last `n` with point `c₁.X` and a binary fan on `c₁.X` and
`f 0`, we can build a fan for all `n+1`.

In `extend_fan_is_limit` we show that if the two given fans are limits, then this fan is also a
limit.
-/
@[simps (config := { rhsMd := semireducible })]
def extend_fan {n : ℕ} {f : Ulift (Finₓ (n+1)) → C} (c₁ : fan fun i : Ulift (Finₓ n) => f ⟨i.down.succ⟩)
  (c₂ : binary_fan (f ⟨0⟩) c₁.X) : fan f :=
  fan.mk c₂.X
    (by 
      rintro ⟨i⟩
      revert i 
      refine' Finₓ.cases _ _
      ·
        apply c₂.fst
      ·
        intro i 
        apply c₂.snd ≫ c₁.π.app (Ulift.up i))

/--
Show that if the two given fans in `extend_fan` are limits, then the constructed fan is also a
limit.
-/
def extend_fan_is_limit {n : ℕ} (f : Ulift (Finₓ (n+1)) → C) {c₁ : fan fun i : Ulift (Finₓ n) => f ⟨i.down.succ⟩}
  {c₂ : binary_fan (f ⟨0⟩) c₁.X} (t₁ : is_limit c₁) (t₂ : is_limit c₂) : is_limit (extend_fan c₁ c₂) :=
  { lift :=
      fun s =>
        by 
          apply (binary_fan.is_limit.lift' t₂ (s.π.app ⟨0⟩) _).1
          apply t₁.lift ⟨_, discrete.nat_trans fun i => s.π.app ⟨i.down.succ⟩⟩,
    fac' :=
      fun s =>
        by 
          rintro ⟨j⟩
          apply Finₓ.inductionOn j
          ·
            apply (binary_fan.is_limit.lift' t₂ _ _).2.1
          ·
            rintro i -
            dsimp only [extend_fan_π_app]
            rw [Finₓ.cases_succ, ←assoc, (binary_fan.is_limit.lift' t₂ _ _).2.2, t₁.fac]
            rfl,
    uniq' :=
      fun s m w =>
        by 
          apply binary_fan.is_limit.hom_ext t₂
          ·
            rw [(binary_fan.is_limit.lift' t₂ _ _).2.1]
            apply w ⟨0⟩
          ·
            rw [(binary_fan.is_limit.lift' t₂ _ _).2.2]
            apply t₁.uniq ⟨_, _⟩
            rintro ⟨j⟩
            rw [assoc]
            dsimp only [discrete.nat_trans_app]
            rw [←w ⟨j.succ⟩]
            dsimp only [extend_fan_π_app]
            rw [Finₓ.cases_succ] }

section 

variable[has_binary_products.{v} C][has_terminal C]

-- error in CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `C` has a terminal object and binary products, then it has a product for objects indexed by
`ulift (fin n)`.
This is a helper lemma for `has_finite_products_of_has_binary_and_terminal`, which is more general
than this.
-/ private theorem has_product_ulift_fin : ∀ (n : exprℕ()) (f : ulift (fin n) → C), has_product f
| 0 := λ f, begin
  letI [] [":", expr has_limits_of_shape (discrete (ulift (fin 0))) C] [":=", expr has_limits_of_shape_of_equivalence (discrete.equivalence (equiv.ulift.trans fin_zero_equiv').symm)],
  apply_instance
end
| «expr + »(n, 1) := λ f, begin
  haveI [] [] [":=", expr has_product_ulift_fin n],
  apply [expr has_limit.mk ⟨_, extend_fan_is_limit f (limit.is_limit _) (limit.is_limit _)⟩]
end

-- error in CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `C` has a terminal object and binary products, then it has limits of shape
`discrete (ulift (fin n))` for any `n : ℕ`.
This is a helper lemma for `has_finite_products_of_has_binary_and_terminal`, which is more general
than this.
-/ private theorem has_limits_of_shape_ulift_fin (n : exprℕ()) : has_limits_of_shape (discrete (ulift (fin n))) C :=
{ has_limit := λ K, begin
    letI [] [] [":=", expr has_product_ulift_fin n K.obj],
    let [] [":", expr «expr ≅ »(discrete.functor K.obj, K)] [":=", expr discrete.nat_iso (λ i, iso.refl _)],
    apply [expr has_limit_of_iso this]
  end }

/-- If `C` has a terminal object and binary products, then it has finite products. -/
theorem has_finite_products_of_has_binary_and_terminal : has_finite_products C :=
  ⟨fun J 𝒥₁ 𝒥₂ =>
      by 
        skip 
        let e := Fintype.equivFin J 
        apply has_limits_of_shape_of_equivalence (discrete.equivalence (e.trans equiv.ulift.symm)).symm 
        refine' has_limits_of_shape_ulift_fin (Fintype.card J)⟩

end 

section Preserves

variable(F : C ⥤ D)

variable[preserves_limits_of_shape (discrete walking_pair) F]

variable[preserves_limits_of_shape (discrete Pempty) F]

variable[has_finite_products.{v} C]

-- error in CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `F` preserves the terminal object and binary products, then it preserves products indexed by
`ulift (fin n)` for any `n`.
-/
noncomputable
def preserves_fin_of_preserves_binary_and_terminal : ∀
(n : exprℕ())
(f : ulift (fin n) → C), preserves_limit (discrete.functor f) F
| 0 := λ f, begin
  letI [] [":", expr preserves_limits_of_shape (discrete (ulift (fin 0))) F] [":=", expr preserves_limits_of_shape_of_equiv (discrete.equivalence (equiv.ulift.trans fin_zero_equiv').symm) _],
  apply_instance
end
| «expr + »(n, 1) := begin
  haveI [] [] [":=", expr preserves_fin_of_preserves_binary_and_terminal n],
  intro [ident f],
  refine [expr preserves_limit_of_preserves_limit_cone (extend_fan_is_limit f (limit.is_limit _) (limit.is_limit _)) _],
  apply [expr (is_limit_map_cone_fan_mk_equiv _ _ _).symm _],
  let [] [] [":=", expr extend_fan_is_limit (λ
    i, F.obj (f i)) (is_limit_of_has_product_of_preserves_limit F _) (is_limit_of_has_binary_product_of_preserves_limit F _ _)],
  refine [expr is_limit.of_iso_limit this _],
  apply [expr cones.ext _ _],
  apply [expr iso.refl _],
  rintro ["⟨", ident j, "⟩"],
  apply [expr fin.induction_on j],
  { apply [expr (category.id_comp _).symm] },
  { rintro [ident i, "-"],
    dsimp ["only"] ["[", expr extend_fan_π_app, ",", expr iso.refl_hom, ",", expr fan.mk_π_app, "]"] [] [],
    rw ["[", expr fin.cases_succ, ",", expr fin.cases_succ, "]"] [],
    change [expr «expr = »(«expr ≫ »(F.map _, _), «expr ≫ »(«expr𝟙»() _, _))] [] [],
    rw ["[", expr id_comp, ",", "<-", expr F.map_comp, "]"] [],
    refl }
end

-- error in CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `F` preserves the terminal object and binary products, then it preserves limits of shape
`discrete (ulift (fin n))`.
-/
def preserves_ulift_fin_of_preserves_binary_and_terminal
(n : exprℕ()) : preserves_limits_of_shape (discrete (ulift (fin n))) F :=
{ preserves_limit := λ K, begin
    let [] [":", expr «expr ≅ »(discrete.functor K.obj, K)] [":=", expr discrete.nat_iso (λ i, iso.refl _)],
    haveI [] [] [":=", expr preserves_fin_of_preserves_binary_and_terminal F n K.obj],
    apply [expr preserves_limit_of_iso_diagram F this]
  end }

-- error in CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `F` preserves the terminal object and binary products then it preserves finite products. -/
def preserves_finite_products_of_preserves_binary_and_terminal
(J : Type v)
[fintype J] : preserves_limits_of_shape.{v} (discrete J) F :=
begin
  classical,
  let [ident e] [] [":=", expr fintype.equiv_fin J],
  haveI [] [] [":=", expr preserves_ulift_fin_of_preserves_binary_and_terminal F (fintype.card J)],
  apply [expr preserves_limits_of_shape_of_equiv (discrete.equivalence (e.trans equiv.ulift.symm)).symm]
end

end Preserves

/--
Given `n+1` objects of `C`, a cofan for the last `n` with point `c₁.X`
and a binary cofan on `c₁.X` and `f 0`, we can build a cofan for all `n+1`.

In `extend_cofan_is_colimit` we show that if the two given cofans are colimits,
then this cofan is also a colimit.
-/
@[simps (config := { rhsMd := semireducible })]
def extend_cofan {n : ℕ} {f : Ulift (Finₓ (n+1)) → C} (c₁ : cofan fun i : Ulift (Finₓ n) => f ⟨i.down.succ⟩)
  (c₂ : binary_cofan (f ⟨0⟩) c₁.X) : cofan f :=
  cofan.mk c₂.X
    (by 
      rintro ⟨i⟩
      revert i 
      refine' Finₓ.cases _ _
      ·
        apply c₂.inl
      ·
        intro i 
        apply c₁.ι.app (Ulift.up i) ≫ c₂.inr)

/--
Show that if the two given cofans in `extend_cofan` are colimits,
then the constructed cofan is also a colimit.
-/
def extend_cofan_is_colimit {n : ℕ} (f : Ulift (Finₓ (n+1)) → C) {c₁ : cofan fun i : Ulift (Finₓ n) => f ⟨i.down.succ⟩}
  {c₂ : binary_cofan (f ⟨0⟩) c₁.X} (t₁ : is_colimit c₁) (t₂ : is_colimit c₂) : is_colimit (extend_cofan c₁ c₂) :=
  { desc :=
      fun s =>
        by 
          apply (binary_cofan.is_colimit.desc' t₂ (s.ι.app ⟨0⟩) _).1
          apply t₁.desc ⟨_, discrete.nat_trans fun i => s.ι.app ⟨i.down.succ⟩⟩,
    fac' :=
      fun s =>
        by 
          rintro ⟨j⟩
          apply Finₓ.inductionOn j
          ·
            apply (binary_cofan.is_colimit.desc' t₂ _ _).2.1
          ·
            rintro i -
            dsimp only [extend_cofan_ι_app]
            rw [Finₓ.cases_succ, assoc, (binary_cofan.is_colimit.desc' t₂ _ _).2.2, t₁.fac]
            rfl,
    uniq' :=
      fun s m w =>
        by 
          apply binary_cofan.is_colimit.hom_ext t₂
          ·
            rw [(binary_cofan.is_colimit.desc' t₂ _ _).2.1]
            apply w ⟨0⟩
          ·
            rw [(binary_cofan.is_colimit.desc' t₂ _ _).2.2]
            apply t₁.uniq ⟨_, _⟩
            rintro ⟨j⟩
            dsimp only [discrete.nat_trans_app]
            rw [←w ⟨j.succ⟩]
            dsimp only [extend_cofan_ι_app]
            rw [Finₓ.cases_succ, assoc] }

section 

variable[has_binary_coproducts.{v} C][has_initial C]

-- error in CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `C` has an initial object and binary coproducts, then it has a coproduct for objects indexed by
`ulift (fin n)`.
This is a helper lemma for `has_cofinite_products_of_has_binary_and_terminal`, which is more general
than this.
-/ private theorem has_coproduct_ulift_fin : ∀ (n : exprℕ()) (f : ulift (fin n) → C), has_coproduct f
| 0 := λ f, begin
  letI [] [":", expr has_colimits_of_shape (discrete (ulift (fin 0))) C] [":=", expr has_colimits_of_shape_of_equivalence (discrete.equivalence (equiv.ulift.trans fin_zero_equiv').symm)],
  apply_instance
end
| «expr + »(n, 1) := λ f, begin
  haveI [] [] [":=", expr has_coproduct_ulift_fin n],
  apply [expr has_colimit.mk ⟨_, extend_cofan_is_colimit f (colimit.is_colimit _) (colimit.is_colimit _)⟩]
end

-- error in CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `C` has an initial object and binary coproducts, then it has colimits of shape
`discrete (ulift (fin n))` for any `n : ℕ`.
This is a helper lemma for `has_cofinite_products_of_has_binary_and_terminal`, which is more general
than this.
-/ private theorem has_colimits_of_shape_ulift_fin (n : exprℕ()) : has_colimits_of_shape (discrete (ulift (fin n))) C :=
{ has_colimit := λ K, begin
    letI [] [] [":=", expr has_coproduct_ulift_fin n K.obj],
    let [] [":", expr «expr ≅ »(K, discrete.functor K.obj)] [":=", expr discrete.nat_iso (λ i, iso.refl _)],
    apply [expr has_colimit_of_iso this]
  end }

/-- If `C` has an initial object and binary coproducts, then it has finite coproducts. -/
theorem has_finite_coproducts_of_has_binary_and_terminal : has_finite_coproducts C :=
  ⟨fun J 𝒥₁ 𝒥₂ =>
      by 
        skip 
        let e := Fintype.equivFin J 
        apply has_colimits_of_shape_of_equivalence (discrete.equivalence (e.trans equiv.ulift.symm)).symm 
        refine' has_colimits_of_shape_ulift_fin (Fintype.card J)⟩

end 

section Preserves

variable(F : C ⥤ D)

variable[preserves_colimits_of_shape (discrete walking_pair) F]

variable[preserves_colimits_of_shape (discrete Pempty) F]

variable[has_finite_coproducts.{v} C]

-- error in CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `F` preserves the initial object and binary coproducts, then it preserves products indexed by
`ulift (fin n)` for any `n`.
-/
noncomputable
def preserves_fin_of_preserves_binary_and_initial : ∀
(n : exprℕ())
(f : ulift (fin n) → C), preserves_colimit (discrete.functor f) F
| 0 := λ f, begin
  letI [] [":", expr preserves_colimits_of_shape (discrete (ulift (fin 0))) F] [":=", expr preserves_colimits_of_shape_of_equiv (discrete.equivalence (equiv.ulift.trans fin_zero_equiv').symm) _],
  apply_instance
end
| «expr + »(n, 1) := begin
  haveI [] [] [":=", expr preserves_fin_of_preserves_binary_and_initial n],
  intro [ident f],
  refine [expr preserves_colimit_of_preserves_colimit_cocone (extend_cofan_is_colimit f (colimit.is_colimit _) (colimit.is_colimit _)) _],
  apply [expr (is_colimit_map_cocone_cofan_mk_equiv _ _ _).symm _],
  let [] [] [":=", expr extend_cofan_is_colimit (λ
    i, F.obj (f i)) (is_colimit_of_has_coproduct_of_preserves_colimit F _) (is_colimit_of_has_binary_coproduct_of_preserves_colimit F _ _)],
  refine [expr is_colimit.of_iso_colimit this _],
  apply [expr cocones.ext _ _],
  apply [expr iso.refl _],
  rintro ["⟨", ident j, "⟩"],
  apply [expr fin.induction_on j],
  { apply [expr category.comp_id] },
  { rintro [ident i, "-"],
    dsimp ["only"] ["[", expr extend_cofan_ι_app, ",", expr iso.refl_hom, ",", expr cofan.mk_ι_app, "]"] [] [],
    rw ["[", expr fin.cases_succ, ",", expr fin.cases_succ, "]"] [],
    erw ["[", expr comp_id, ",", "<-", expr F.map_comp, "]"] [],
    refl }
end

-- error in CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `F` preserves the initial object and binary coproducts, then it preserves colimits of shape
`discrete (ulift (fin n))`.
-/
def preserves_ulift_fin_of_preserves_binary_and_initial
(n : exprℕ()) : preserves_colimits_of_shape (discrete (ulift (fin n))) F :=
{ preserves_colimit := λ K, begin
    let [] [":", expr «expr ≅ »(discrete.functor K.obj, K)] [":=", expr discrete.nat_iso (λ i, iso.refl _)],
    haveI [] [] [":=", expr preserves_fin_of_preserves_binary_and_initial F n K.obj],
    apply [expr preserves_colimit_of_iso_diagram F this]
  end }

-- error in CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `F` preserves the initial object and binary coproducts then it preserves finite products. -/
def preserves_finite_coproducts_of_preserves_binary_and_initial
(J : Type v)
[fintype J] : preserves_colimits_of_shape.{v} (discrete J) F :=
begin
  classical,
  let [ident e] [] [":=", expr fintype.equiv_fin J],
  haveI [] [] [":=", expr preserves_ulift_fin_of_preserves_binary_and_initial F (fintype.card J)],
  apply [expr preserves_colimits_of_shape_of_equiv (discrete.equivalence (e.trans equiv.ulift.symm)).symm]
end

end Preserves

end CategoryTheory

