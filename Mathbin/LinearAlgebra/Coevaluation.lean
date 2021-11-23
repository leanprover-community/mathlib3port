import Mathbin.LinearAlgebra.Contraction 
import Mathbin.LinearAlgebra.FiniteDimensional 
import Mathbin.LinearAlgebra.Dual

/-!
# The coevaluation map on finite dimensional vector spaces

Given a finite dimensional vector space `V` over a field `K` this describes the canonical linear map
from `K` to `V ⊗ dual K V` which corresponds to the identity function on `V`.

## Tags

coevaluation, dual module, tensor product

## Future work

* Prove that this is independent of the choice of basis on `V`.
-/


noncomputable theory

section coevaluation

open TensorProduct FiniteDimensional

open_locale TensorProduct BigOperators

universe u v

variable(K : Type u)[Field K]

variable(V : Type v)[AddCommGroupₓ V][Module K V][FiniteDimensional K V]

/-- The coevaluation map is a linear map from a field `K` to a finite dimensional
  vector space `V`. -/
def coevaluation : K →ₗ[K] V ⊗[K] Module.Dual K V :=
  let bV := Basis.ofVectorSpace K V
  (Basis.singleton Unit K).constr K$ fun _ => ∑i : Basis.OfVectorSpaceIndex K V, bV i ⊗ₜ[K] bV.coord i

theorem coevaluation_apply_one :
  (coevaluation K V) (1 : K) =
    let bV := Basis.ofVectorSpace K V
    ∑i : Basis.OfVectorSpaceIndex K V, bV i ⊗ₜ[K] bV.coord i :=
  by 
    simp only [coevaluation, id]
    rw [(Basis.singleton Unit K).constr_apply_fintype K]
    simp only [Fintype.univ_punit, Finset.sum_const, one_smul, Basis.singleton_repr, Basis.equiv_fun_apply,
      Basis.coe_of_vector_space, one_nsmul, Finset.card_singleton]

open TensorProduct

-- error in LinearAlgebra.Coevaluation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- This lemma corresponds to one of the coherence laws for duals in rigid categories, see
  `category_theory.monoidal.rigid`. -/
theorem contract_left_assoc_coevaluation : «expr = »(«expr ∘ₗ »((contract_left K V).rtensor _, «expr ∘ₗ »((tensor_product.assoc K _ _ _).symm.to_linear_map, (coevaluation K V).ltensor (module.dual K V))), «expr ∘ₗ »((tensor_product.lid K _).symm.to_linear_map, (tensor_product.rid K _).to_linear_map)) :=
begin
  letI [] [] [":=", expr classical.dec_eq (basis.of_vector_space_index K V)],
  apply [expr tensor_product.ext],
  apply [expr (basis.of_vector_space K V).dual_basis.ext],
  intro [ident j],
  apply [expr linear_map.ext_ring],
  rw ["[", expr linear_map.compr₂_apply, ",", expr linear_map.compr₂_apply, ",", expr tensor_product.mk_apply, "]"] [],
  simp [] [] ["only"] ["[", expr linear_map.coe_comp, ",", expr function.comp_app, ",", expr linear_equiv.coe_to_linear_map, "]"] [] [],
  rw ["[", expr rid_tmul, ",", expr one_smul, ",", expr lid_symm_apply, "]"] [],
  simp [] [] ["only"] ["[", expr linear_equiv.coe_to_linear_map, ",", expr linear_map.ltensor_tmul, ",", expr coevaluation_apply_one, "]"] [] [],
  rw ["[", expr tensor_product.tmul_sum, ",", expr linear_equiv.map_sum, "]"] [],
  simp [] [] ["only"] ["[", expr assoc_symm_tmul, "]"] [] [],
  rw ["[", expr linear_map.map_sum, "]"] [],
  simp [] [] ["only"] ["[", expr linear_map.rtensor_tmul, ",", expr contract_left_apply, "]"] [] [],
  simp [] [] ["only"] ["[", expr basis.coe_dual_basis, ",", expr basis.coord_apply, ",", expr basis.repr_self_apply, ",", expr tensor_product.ite_tmul, "]"] [] [],
  rw ["[", expr finset.sum_ite_eq', "]"] [],
  simp [] [] ["only"] ["[", expr finset.mem_univ, ",", expr if_true, "]"] [] []
end

-- error in LinearAlgebra.Coevaluation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- This lemma corresponds to one of the coherence laws for duals in rigid categories, see
  `category_theory.monoidal.rigid`. -/
theorem contract_left_assoc_coevaluation' : «expr = »(«expr ∘ₗ »((contract_left K V).ltensor _, «expr ∘ₗ »((tensor_product.assoc K _ _ _).to_linear_map, (coevaluation K V).rtensor V)), «expr ∘ₗ »((tensor_product.rid K _).symm.to_linear_map, (tensor_product.lid K _).to_linear_map)) :=
begin
  letI [] [] [":=", expr classical.dec_eq (basis.of_vector_space_index K V)],
  apply [expr tensor_product.ext],
  apply [expr linear_map.ext_ring],
  apply [expr (basis.of_vector_space K V).ext],
  intro [ident j],
  rw ["[", expr linear_map.compr₂_apply, ",", expr linear_map.compr₂_apply, ",", expr tensor_product.mk_apply, "]"] [],
  simp [] [] ["only"] ["[", expr linear_map.coe_comp, ",", expr function.comp_app, ",", expr linear_equiv.coe_to_linear_map, "]"] [] [],
  rw ["[", expr lid_tmul, ",", expr one_smul, ",", expr rid_symm_apply, "]"] [],
  simp [] [] ["only"] ["[", expr linear_equiv.coe_to_linear_map, ",", expr linear_map.rtensor_tmul, ",", expr coevaluation_apply_one, "]"] [] [],
  rw ["[", expr tensor_product.sum_tmul, ",", expr linear_equiv.map_sum, "]"] [],
  simp [] [] ["only"] ["[", expr assoc_tmul, "]"] [] [],
  rw ["[", expr linear_map.map_sum, "]"] [],
  simp [] [] ["only"] ["[", expr linear_map.ltensor_tmul, ",", expr contract_left_apply, "]"] [] [],
  simp [] [] ["only"] ["[", expr basis.coord_apply, ",", expr basis.repr_self_apply, ",", expr tensor_product.tmul_ite, "]"] [] [],
  rw ["[", expr finset.sum_ite_eq, "]"] [],
  simp [] [] ["only"] ["[", expr finset.mem_univ, ",", expr if_true, "]"] [] []
end

end coevaluation

