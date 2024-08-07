/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import LinearAlgebra.QuadraticForm.IsometryEquiv
import LinearAlgebra.QuadraticForm.Prod

#align_import linear_algebra.quadratic_form.dual from "leanprover-community/mathlib"@"d11f435d4e34a6cea0a1797d6b625b0c170be845"

/-!
# Quadratic form structures related to `module.dual`

## Main definitions

* `bilin_form.dual_prod R M`, the bilinear form on `(f, x) : module.dual R M × M` defined as
  `f x`.
* `quadratic_form.dual_prod R M`, the quadratic form on `(f, x) : module.dual R M × M` defined as
  `f x`.
* `quadratic_form.to_dual_prod : M × M →ₗ[R] module.dual R M × M` a form-preserving map from
  `(Q.prod $ -Q)` to `quadratic_form.dual_prod R M`. Note that we do not have the morphism
  version of `quadratic_form.isometry`, so for now this is stated without full bundling.

-/


variable (R M N : Type _)

namespace BilinForm

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

#print LinearMap.dualProd /-
/-- The symmetric bilinear form on `module.dual R M × M` defined as
`B (f, x) (g, y) = f y + g x`. -/
@[simps]
def dualProd : BilinForm R (Module.Dual R M × M) :=
  LinearMap.toBilin <|
    (LinearMap.applyₗ.comp (LinearMap.snd R (Module.Dual R M) M)).compl₂
        (LinearMap.fst R (Module.Dual R M) M) +
      ((LinearMap.applyₗ.comp (LinearMap.snd R (Module.Dual R M) M)).compl₂
          (LinearMap.fst R (Module.Dual R M) M)).flip
#align bilin_form.dual_prod LinearMap.dualProd
-/

#print LinearMap.isSymm_dualProd /-
theorem isSymm_dualProd : (dualProd R M).IsSymm := fun x y => add_comm _ _
#align bilin_form.is_symm_dual_prod LinearMap.isSymm_dualProd
-/

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [Module R M]

#print LinearMap.separatingLeft_dualProd /-
theorem separatingLeft_dualProd :
    (dualProd R M).Nondegenerate ↔ Function.Injective (Module.Dual.eval R M) := by
  classical
  rw [nondegenerate_iff_ker_eq_bot]
  rw [LinearMap.ker_eq_bot]
  let e := LinearEquiv.prodComm R _ _ ≪≫ₗ Module.dualProdDualEquivDual R (Module.Dual R M) M
  let h_d := e.symm.to_linear_map.comp (dual_prod R M).toLin
  refine' (Function.Injective.of_comp_iff e.symm.injective (dual_prod R M).toLin).symm.trans _
  rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  change Function.Injective h_d ↔ _
  have : h_d = LinearMap.prodMap LinearMap.id (Module.Dual.eval R M) :=
    by
    refine' LinearMap.ext fun x => Prod.ext _ _
    · ext
      dsimp [h_d, Module.Dual.eval, LinearEquiv.prodComm]
      simp
    · ext
      dsimp [h_d, Module.Dual.eval, LinearEquiv.prodComm]
      simp
  rw [this, LinearMap.coe_prodMap]
  refine' prod.map_injective.trans _
  exact and_iff_right Function.injective_id
#align bilin_form.nondenerate_dual_prod LinearMap.separatingLeft_dualProd
-/

end Ring

end BilinForm

namespace QuadraticMap

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

#print QuadraticForm.dualProd /-
/-- The quadratic form on `module.dual R M × M` defined as `Q (f, x) = f x`. -/
@[simps]
def dualProd : QuadraticMap R (Module.Dual R M × M)
    where
  toFun p := p.1 p.2
  toFun_smul a p := by
    rw [Prod.smul_fst, Prod.smul_snd, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul,
      smul_eq_mul, mul_assoc]
  exists_companion' :=
    ⟨LinearMap.dualProd R M, fun p q => by
      rw [BilinForm.dualProd_apply, Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add,
        map_add, add_right_comm _ (q.1 q.2), add_comm (q.1 p.2) (p.1 q.2), ← add_assoc, ←
        add_assoc]⟩
#align quadratic_form.dual_prod QuadraticForm.dualProd
-/

#print LinearMap.dualProd.toQuadraticForm /-
@[simp]
theorem LinearMap.dualProd.toQuadraticForm :
    (LinearMap.dualProd R M).toQuadraticMap = 2 • dualProd R M :=
  ext fun a => (two_nsmul _).symm
#align bilin_form.dual_prod.to_quadratic_form LinearMap.dualProd.toQuadraticForm
-/

variable {R M N}

#print QuadraticForm.dualProdIsometry /-
/-- Any module isomorphism induces a quadratic isomorphism between the corresponding `dual_prod.` -/
@[simps]
def dualProdIsometry (f : M ≃ₗ[R] N) : (dualProd R M).IsometryEquivₓ (dualProd R N)
    where
  toLinearEquiv := f.dualMap.symm.Prod f
  map_app' x := DFunLike.congr_arg x.fst <| f.symm_apply_apply _
#align quadratic_form.dual_prod_isometry QuadraticForm.dualProdIsometry
-/

#print QuadraticForm.dualProdProdIsometry /-
/-- `quadratic_form.dual_prod` commutes (isometrically) with `quadratic_form.prod`. -/
@[simps]
def dualProdProdIsometry : (dualProd R (M × N)).IsometryEquivₓ ((dualProd R M).Prod (dualProd R N))
    where
  toLinearEquiv :=
    (Module.dualProdDualEquivDual R M N).symm.Prod (LinearEquiv.refl R (M × N)) ≪≫ₗ
      LinearEquiv.prodProdProdComm R _ _ M N
  map_app' m :=
    (m.fst.map_add _ _).symm.trans <| DFunLike.congr_arg m.fst <| Prod.ext (add_zero _) (zero_add _)
#align quadratic_form.dual_prod_prod_isometry QuadraticForm.dualProdProdIsometry
-/

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [Module R M]

variable {R M}

/-- The isometry sending `(Q.prod $ -Q)` to `(quadratic_form.dual_prod R M)`.

This is `σ` from Proposition 4.8, page 84 of
[*Hermitian K-Theory and Geometric Applications*][hyman1973]; though we swap the order of the pairs.
-/
@[simps]
def toDualProd (Q : QuadraticMap R M) [Invertible (2 : R)] : M × M →ₗ[R] Module.Dual R M × M :=
  LinearMap.prod
    (Q.Associated.toLin.comp (LinearMap.fst _ _ _) + Q.Associated.toLin.comp (LinearMap.snd _ _ _))
    (LinearMap.fst _ _ _ - LinearMap.snd _ _ _)
#align quadratic_form.to_dual_prod QuadraticForm.toDualProdₓ

theorem QuadraticMap.Isometry.map_app [Invertible (2 : R)] (Q : QuadraticMap R M) (x : M × M) :
    QuadraticForm.dualProd R M (toDualProd Q x) = (Q.Prod <| -Q) x :=
  by
  dsimp only [to_dual_prod, Associated, associated_hom]
  dsimp
  simp [polar_comm _ x.1 x.2, ← sub_add, mul_sub, sub_mul, smul_sub, Submonoid.smul_def, ←
    sub_eq_add_neg (Q x.1) (Q x.2)]
#align quadratic_form.to_dual_prod_isometry QuadraticMap.Isometry.map_appₓ

-- TODO: show that `to_dual_prod` is an equivalence
end Ring

end QuadraticMap

