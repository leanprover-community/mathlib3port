/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import RepresentationTheory.FDRep
import LinearAlgebra.Trace
import RepresentationTheory.Invariants

#align_import representation_theory.character from "leanprover-community/mathlib"@"1a51edf13debfcbe223fa06b1cb353b9ed9751cc"

/-!
# Characters of representations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file introduces characters of representation and proves basic lemmas about how characters
behave under various operations on representations.

# TODO
* Once we have the monoidal closed structure on `fdRep k G` and a better API for the rigid
structure, `char_dual` and `char_lin_hom` should probably be stated in terms of `Vᘁ` and `ihom V W`.
-/


noncomputable section

universe u

open CategoryTheory LinearMap CategoryTheory.MonoidalCategory Representation FiniteDimensional

open scoped BigOperators

variable {k : Type u} [Field k]

namespace FDRep

section Monoid

variable {G : Type u} [Monoid G]

#print FDRep.character /-
/-- The character of a representation `V : fdRep k G` is the function associating to `g : G` the
trace of the linear map `V.ρ g`.-/
def character (V : FDRep k G) (g : G) :=
  LinearMap.trace k V (V.ρ g)
#align fdRep.character FDRep.character
-/

#print FDRep.char_mul_comm /-
theorem char_mul_comm (V : FDRep k G) (g : G) (h : G) : V.character (h * g) = V.character (g * h) :=
  by simp only [trace_mul_comm, character, map_mul]
#align fdRep.char_mul_comm FDRep.char_mul_comm
-/

#print FDRep.char_one /-
@[simp]
theorem char_one (V : FDRep k G) : V.character 1 = FiniteDimensional.finrank k V := by
  simp only [character, map_one, trace_one]
#align fdRep.char_one FDRep.char_one
-/

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FDRep.char_tensor /-
/-- The character is multiplicative under the tensor product. -/
@[simp]
theorem char_tensor (V W : FDRep k G) : (V ⊗ W).character = V.character * W.character := by ext g;
  convert trace_tensor_product' (V.ρ g) (W.ρ g)
#align fdRep.char_tensor FDRep.char_tensor
-/

#print FDRep.char_iso /-
/-- The character of isomorphic representations is the same. -/
theorem char_iso {V W : FDRep k G} (i : V ≅ W) : V.character = W.character := by ext g;
  simp only [character, FDRep.Iso.conj_ρ i]; exact (trace_conj' (V.ρ g) _).symm
#align fdRep.char_iso FDRep.char_iso
-/

end Monoid

section Group

variable {G : Type u} [Group G]

#print FDRep.char_conj /-
/-- The character of a representation is constant on conjugacy classes. -/
@[simp]
theorem char_conj (V : FDRep k G) (g : G) (h : G) : V.character (h * g * h⁻¹) = V.character g := by
  rw [char_mul_comm, inv_mul_cancel_left]
#align fdRep.char_conj FDRep.char_conj
-/

#print FDRep.char_dual /-
@[simp]
theorem char_dual (V : FDRep k G) (g : G) : (of (dual V.ρ)).character g = V.character g⁻¹ :=
  trace_transpose' (V.ρ g⁻¹)
#align fdRep.char_dual FDRep.char_dual
-/

#print FDRep.char_linHom /-
@[simp]
theorem char_linHom (V W : FDRep k G) (g : G) :
    (of (linHom V.ρ W.ρ)).character g = V.character g⁻¹ * W.character g := by
  rw [← char_iso (dual_tensor_iso_lin_hom _ _), char_tensor, Pi.mul_apply, char_dual]
#align fdRep.char_lin_hom FDRep.char_linHom
-/

variable [Fintype G] [Invertible (Fintype.card G : k)]

#print FDRep.average_char_eq_finrank_invariants /-
theorem average_char_eq_finrank_invariants (V : FDRep k G) :
    ⅟ (Fintype.card G : k) • ∑ g : G, V.character g = finrank k (invariants V.ρ) := by
  rw [← (is_proj_average_map V.ρ).trace]; simp [character, GroupAlgebra.average, _root_.map_sum]
#align fdRep.average_char_eq_finrank_invariants FDRep.average_char_eq_finrank_invariants
-/

end Group

section Orthogonality

variable {G : Grp.{u}} [IsAlgClosed k]

open scoped Classical

variable [Fintype G] [Invertible (Fintype.card G : k)]

#print FDRep.char_orthonormal /-
/-- Orthogonality of characters for irreducible representations of finite group over an
algebraically closed field whose characteristic doesn't divide the order of the group. -/
theorem char_orthonormal (V W : FDRep k G) [Simple V] [Simple W] :
    ⅟ (Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
      if Nonempty (V ≅ W) then ↑1 else ↑0 :=
  by
  -- First, we can rewrite the summand `V.character g * W.character g⁻¹` as the character
  -- of the representation `V ⊗ W* ≅ Hom(W, V)` applied to `g`.
  conv in
    V.character _ *
      W.character _ =>
    rw [mul_comm, ← char_dual, ← Pi.mul_apply, ← char_tensor]
    rw [char_iso (FDRep.dualTensorIsoLinHom W.ρ V)]
  -- The average over the group of the character of a representation equals the dimension of the
  -- space of invariants.
  rw [average_char_eq_finrank_invariants]
  rw [show (of (lin_hom W.ρ V.ρ)).ρ = lin_hom W.ρ V.ρ from FDRep.of_ρ (lin_hom W.ρ V.ρ)]
  -- The space of invariants of `Hom(W, V)` is the subspace of `G`-equivariant linear maps,
  -- `Hom_G(W, V)`.
  rw [(lin_hom.invariants_equiv_fdRep_hom W V).finrank_eq]
  -- By Schur's Lemma, the dimension of `Hom_G(W, V)` is `1` is `V ≅ W` and `0` otherwise.
  rw_mod_cast [finrank_hom_simple_simple W V, iso.nonempty_iso_symm]
#align fdRep.char_orthonormal FDRep.char_orthonormal
-/

end Orthogonality

end FDRep

