import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks 
import Mathbin.RingTheory.TensorProduct 
import Mathbin.Algebra.Category.CommRing.Basic

/-!
# Explicit pushout cocone for CommRing

In this file we prove that tensor product is indeed the fibered coproduct in `CommRing`, and
provide the explicit pushout cocone.

-/


universe u

open CategoryTheory

open_locale TensorProduct

variable {R A B : CommRingₓₓ.{u}} (f : R ⟶ A) (g : R ⟶ B)

namespace CommRingₓₓ

-- error in Algebra.Category.CommRing.Pushout: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The explicit cocone with tensor products as the fibered product in `CommRing`. -/
def pushout_cocone : limits.pushout_cocone f g :=
begin
  letI [] [] [":=", expr ring_hom.to_algebra f],
  letI [] [] [":=", expr ring_hom.to_algebra g],
  apply [expr limits.pushout_cocone.mk],
  show [expr CommRing],
  from [expr CommRing.of «expr ⊗[ ] »(A, R, B)],
  show [expr «expr ⟶ »(A, _)],
  from [expr algebra.tensor_product.include_left.to_ring_hom],
  show [expr «expr ⟶ »(B, _)],
  from [expr algebra.tensor_product.include_right.to_ring_hom],
  ext [] [ident r] [],
  transitivity [expr algebra_map R «expr ⊗[ ] »(A, R, B) r],
  exact [expr algebra.tensor_product.include_left.commutes r],
  exact [expr (algebra.tensor_product.include_right.commutes r).symm]
end

-- error in Algebra.Category.CommRing.Pushout: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem pushout_cocone_inl : «expr = »((pushout_cocone f g).inl, by { letI [] [] [":=", expr f.to_algebra],
   letI [] [] [":=", expr g.to_algebra],
   exactI [expr algebra.tensor_product.include_left.to_ring_hom] }) :=
rfl

-- error in Algebra.Category.CommRing.Pushout: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem pushout_cocone_inr : «expr = »((pushout_cocone f g).inr, by { letI [] [] [":=", expr f.to_algebra],
   letI [] [] [":=", expr g.to_algebra],
   exactI [expr algebra.tensor_product.include_right.to_ring_hom] }) :=
rfl

-- error in Algebra.Category.CommRing.Pushout: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem pushout_cocone_X : «expr = »((pushout_cocone f g).X, by { letI [] [] [":=", expr f.to_algebra],
   letI [] [] [":=", expr g.to_algebra],
   exactI [expr CommRing.of «expr ⊗[ ] »(A, R, B)] }) :=
rfl

-- error in Algebra.Category.CommRing.Pushout: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Verify that the `pushout_cocone` is indeed the colimit. -/
def pushout_cocone_is_colimit : limits.is_colimit (pushout_cocone f g) :=
limits.pushout_cocone.is_colimit_aux' _ (λ s, begin
   letI [] [] [":=", expr ring_hom.to_algebra f],
   letI [] [] [":=", expr ring_hom.to_algebra g],
   letI [] [] [":=", expr ring_hom.to_algebra «expr ≫ »(f, s.inl)],
   let [ident f'] [":", expr «expr →ₐ[ ] »(A, R, s.X)] [":=", expr { commutes' := λ
      r, by { change [expr «expr = »(s.inl.to_fun (f r), «expr ≫ »(f, s.inl) r)] [] [],
        refl },
      ..s.inl }],
   let [ident g'] [":", expr «expr →ₐ[ ] »(B, R, s.X)] [":=", expr { commutes' := λ
      r, by { change [expr «expr = »(«expr ≫ »(g, s.inr) r, «expr ≫ »(f, s.inl) r)] [] [],
        congr' [1] [],
        exact [expr (s.ι.naturality limits.walking_span.hom.snd).trans (s.ι.naturality limits.walking_span.hom.fst).symm] },
      ..s.inr }],
   use [expr alg_hom.to_ring_hom (algebra.tensor_product.product_map f' g')],
   simp [] [] ["only"] ["[", expr pushout_cocone_inl, ",", expr pushout_cocone_inr, "]"] [] [],
   split,
   { ext [] [ident x] [],
     exact [expr algebra.tensor_product.product_map_left_apply _ _ x] },
   split,
   { ext [] [ident x] [],
     exact [expr algebra.tensor_product.product_map_right_apply _ _ x] },
   intros [ident h, ident eq1, ident eq2],
   let [ident h'] [":", expr «expr →ₐ[ ] »(«expr ⊗[ ] »(A, R, B), R, s.X)] [":=", expr { commutes' := λ
      r, by { change [expr «expr = »(h «expr ⊗ₜ[ ] »(f r, R, 1), s.inl (f r))] [] [],
        rw ["<-", expr eq1] [],
        simp [] [] [] [] [] [] },
      ..h }],
   suffices [] [":", expr «expr = »(h', algebra.tensor_product.product_map f' g')],
   { ext [] [ident x] [],
     change [expr «expr = »(h' x, algebra.tensor_product.product_map f' g' x)] [] [],
     rw [expr this] [] },
   apply [expr algebra.tensor_product.ext],
   intros [ident a, ident b],
   simp [] [] [] ["[", "<-", expr eq1, ",", "<-", expr eq2, ",", "<-", expr h.map_mul, "]"] [] []
 end)

end CommRingₓₓ

