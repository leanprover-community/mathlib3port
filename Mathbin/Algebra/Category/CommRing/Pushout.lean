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

variable{R A B : CommRingₓₓ.{u}}(f : R ⟶ A)(g : R ⟶ B)

namespace CommRingₓₓ

/-- The explicit cocone with tensor products as the fibered product in `CommRing`. -/
def pushout_cocone : limits.pushout_cocone f g :=
  by 
    letI this := RingHom.toAlgebra f 
    letI this := RingHom.toAlgebra g 
    apply limits.pushout_cocone.mk 
    show CommRingₓₓ 
    exact CommRingₓₓ.of (A ⊗[R] B)
    show A ⟶ _ 
    exact algebra.tensor_product.include_left.to_ring_hom 
    show B ⟶ _ 
    exact algebra.tensor_product.include_right.to_ring_hom 
    ext r 
    trans algebraMap R (A ⊗[R] B) r 
    exact algebra.tensor_product.include_left.commutes r 
    exact (algebra.tensor_product.include_right.commutes r).symm

@[simp]
theorem pushout_cocone_inl :
  (pushout_cocone f g).inl =
    by 
      letI this := f.to_algebra 
      letI this := g.to_algebra 
      exactI algebra.tensor_product.include_left.to_ring_hom :=
  rfl

@[simp]
theorem pushout_cocone_inr :
  (pushout_cocone f g).inr =
    by 
      letI this := f.to_algebra 
      letI this := g.to_algebra 
      exactI algebra.tensor_product.include_right.to_ring_hom :=
  rfl

@[simp]
theorem pushout_cocone_X :
  (pushout_cocone f g).x =
    by 
      letI this := f.to_algebra 
      letI this := g.to_algebra 
      exactI CommRingₓₓ.of (A ⊗[R] B) :=
  rfl

/-- Verify that the `pushout_cocone` is indeed the colimit. -/
def pushout_cocone_is_colimit : limits.is_colimit (pushout_cocone f g) :=
  limits.pushout_cocone.is_colimit_aux' _
    fun s =>
      by 
        letI this := RingHom.toAlgebra f 
        letI this := RingHom.toAlgebra g 
        letI this := RingHom.toAlgebra (f ≫ s.inl)
        let f' : A →ₐ[R] s.X :=
          { s.inl with
            commutes' :=
              fun r =>
                by 
                  change s.inl.to_fun (f r) = (f ≫ s.inl) r 
                  rfl }
        let g' : B →ₐ[R] s.X :=
          { s.inr with
            commutes' :=
              fun r =>
                by 
                  change (g ≫ s.inr) r = (f ≫ s.inl) r 
                  congr 1 
                  exact
                    (s.ι.naturality limits.walking_span.hom.snd).trans
                      (s.ι.naturality limits.walking_span.hom.fst).symm }
        use AlgHom.toRingHom (Algebra.TensorProduct.productMap f' g')
        simp only [pushout_cocone_inl, pushout_cocone_inr]
        split 
        ·
          ext x 
          exact Algebra.TensorProduct.product_map_left_apply _ _ x 
        split 
        ·
          ext x 
          exact Algebra.TensorProduct.product_map_right_apply _ _ x 
        intro h eq1 eq2 
        let h' : A ⊗[R] B →ₐ[R] s.X :=
          { h with
            commutes' :=
              fun r =>
                by 
                  change h (f r ⊗ₜ[R] 1) = s.inl (f r)
                  rw [←eq1]
                  simp  }
        suffices  : h' = Algebra.TensorProduct.productMap f' g'
        ·
          ext x 
          change h' x = Algebra.TensorProduct.productMap f' g' x 
          rw [this]
        apply Algebra.TensorProduct.ext 
        intro a b 
        simp [←eq1, ←eq2, ←h.map_mul]

end CommRingₓₓ

