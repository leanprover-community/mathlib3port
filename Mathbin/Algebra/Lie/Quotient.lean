import Mathbin.Algebra.Lie.Submodule 
import Mathbin.Algebra.Lie.OfAssociative

/-!
# Quotients of Lie algebras and Lie modules

Given a Lie submodule of a Lie module, the quotient carries a natural Lie module structure. In the
special case that the Lie module is the Lie algebra itself via the adjoint action, the submodule
is a Lie ideal and the quotient carries a natural Lie algebra structure.

We define these quotient structures here. A notable omission at the time of writing (February 2021)
is a statement and proof of the universal property of these quotients.

## Main definitions

  * `lie_submodule.quotient.lie_quotient_lie_module`
  * `lie_submodule.quotient.lie_quotient_lie_algebra`

## Tags

lie algebra, quotient
-/


universe u v w w₁ w₂

namespace LieSubmodule

variable{R : Type u}{L : Type v}{M : Type w}

variable[CommRingₓ R][LieRing L][LieAlgebra R L][AddCommGroupₓ M][Module R M]

variable[LieRingModule L M][LieModule R L M]

variable(N N' : LieSubmodule R L M)(I J : LieIdeal R L)

/-- The quotient of a Lie module by a Lie submodule. It is a Lie module. -/
abbrev Quotientₓ :=
  N.to_submodule.quotient

namespace Quotientₓ

variable{N I}

/-- Map sending an element of `M` to the corresponding element of `M/N`, when `N` is a
lie_submodule of the lie_module `N`. -/
abbrev mk : M → N.quotient :=
  Submodule.Quotient.mk

theorem is_quotient_mk (m : M) : Quotientₓ.mk' m = (mk m : N.quotient) :=
  rfl

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural linear map from `L` to the endomorphisms of `M` leaving `N` invariant. -/
def lie_submodule_invariant : L →ₗ[R] Submodule.compatibleMaps N.to_submodule N.to_submodule :=
  LinearMap.codRestrict _ (LieModule.toEndomorphism R L M) N.lie_mem

variable(N)

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural Lie algebra morphism from `L` to the linear endomorphism of the quotient `M/N`. -/
def action_as_endo_map : L →ₗ⁅R⁆ Module.End R N.quotient :=
  { LinearMap.comp (Submodule.mapqLinear (N : Submodule R M) («expr↑ » N)) lie_submodule_invariant with
    map_lie' :=
      fun x y =>
        by 
          ext m 
          change mk ⁅⁅x,y⁆,m⁆ = mk (⁅x,⁅y,m⁆⁆ - ⁅y,⁅x,m⁆⁆)
          congr 
          apply lie_lie }

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there is
a natural bracket action of `L` on the quotient `M/N`. -/
def action_as_endo_map_bracket : HasBracket L N.quotient :=
  ⟨fun x n => action_as_endo_map N x n⟩

instance lie_quotient_lie_ring_module : LieRingModule L N.quotient :=
  { bracket := fun x n => (action_as_endo_map N : L →ₗ[R] Module.End R N.quotient) x n,
    add_lie :=
      fun x y n =>
        by 
          simp only [LinearMap.map_add, LinearMap.add_apply],
    lie_add :=
      fun x m n =>
        by 
          simp only [LinearMap.map_add, LinearMap.add_apply],
    leibniz_lie :=
      fun x y m =>
        show action_as_endo_map _ _ _ = _ by 
          simp only [LieHom.map_lie, LieRing.of_associative_ring_bracket, sub_add_cancel, LieHom.coe_to_linear_map,
            LinearMap.mul_apply, LinearMap.sub_apply] }

/-- The quotient of a Lie module by a Lie submodule, is a Lie module. -/
instance lie_quotient_lie_module : LieModule R L N.quotient :=
  { smul_lie :=
      fun t x m =>
        show (_ : L →ₗ[R] Module.End R N.quotient) _ _ = _ by 
          simp only [LinearMap.map_smul]
          rfl,
    lie_smul :=
      fun x t m =>
        show (_ : L →ₗ[R] Module.End R N.quotient) _ _ = _ by 
          simp only [LinearMap.map_smul]
          rfl }

-- error in Algebra.Lie.Quotient: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance lie_quotient_has_bracket : has_bracket (quotient I) (quotient I) :=
⟨begin
   intros [ident x, ident y],
   apply [expr quotient.lift_on₂' x y (λ x' y', mk «expr⁅ , ⁆»(x', y'))],
   intros [ident x₁, ident x₂, ident y₁, ident y₂, ident h₁, ident h₂],
   apply [expr (submodule.quotient.eq I.to_submodule).2],
   have [ident h] [":", expr «expr = »(«expr - »(«expr⁅ , ⁆»(x₁, x₂), «expr⁅ , ⁆»(y₁, y₂)), «expr + »(«expr⁅ , ⁆»(x₁, «expr - »(x₂, y₂)), «expr⁅ , ⁆»(«expr - »(x₁, y₁), y₂)))] [],
   by simp [] [] [] ["[", "-", ident lie_skew, ",", expr sub_eq_add_neg, ",", expr add_assoc, "]"] [] [],
   rw [expr h] [],
   apply [expr submodule.add_mem],
   { apply [expr lie_mem_right R L I x₁ «expr - »(x₂, y₂) h₂] },
   { apply [expr lie_mem_left R L I «expr - »(x₁, y₁) y₂ h₁] }
 end⟩

@[simp]
theorem mk_bracket (x y : L) : mk ⁅x,y⁆ = ⁅(mk x : Quotientₓ I),(mk y : Quotientₓ I)⁆ :=
  rfl

instance lie_quotient_lie_ring : LieRing (Quotientₓ I) :=
  { add_lie :=
      by 
        intro x' y' z' 
        apply Quotientₓ.induction_on₃' x' y' z' 
        intro x y z 
        repeat' 
          first |
            rw [is_quotient_mk]|
            rw [←mk_bracket]|
            rw [←Submodule.Quotient.mk_add]
        apply congr_argₓ 
        apply add_lie,
    lie_add :=
      by 
        intro x' y' z' 
        apply Quotientₓ.induction_on₃' x' y' z' 
        intro x y z 
        repeat' 
          first |
            rw [is_quotient_mk]|
            rw [←mk_bracket]|
            rw [←Submodule.Quotient.mk_add]
        apply congr_argₓ 
        apply lie_add,
    lie_self :=
      by 
        intro x' 
        apply Quotientₓ.induction_on' x' 
        intro x 
        rw [is_quotient_mk, ←mk_bracket]
        apply congr_argₓ 
        apply lie_self,
    leibniz_lie :=
      by 
        intro x' y' z' 
        apply Quotientₓ.induction_on₃' x' y' z' 
        intro x y z 
        repeat' 
          first |
            rw [is_quotient_mk]|
            rw [←mk_bracket]|
            rw [←Submodule.Quotient.mk_add]
        apply congr_argₓ 
        apply leibniz_lie }

instance lie_quotient_lie_algebra : LieAlgebra R (Quotientₓ I) :=
  { lie_smul :=
      by 
        intro t x' y' 
        apply Quotientₓ.induction_on₂' x' y' 
        intro x y 
        repeat' 
          first |
            rw [is_quotient_mk]|
            rw [←mk_bracket]|
            rw [←Submodule.Quotient.mk_smul]
        apply congr_argₓ 
        apply lie_smul }

/-- `lie_submodule.quotient.mk` as a `lie_module_hom`. -/
@[simps]
def mk' : M →ₗ⁅R,L⁆ Quotientₓ N :=
  { N.to_submodule.mkq with toFun := mk, map_lie' := fun r m => rfl }

/-- Two `lie_module_hom`s from a quotient lie module are equal if their compositions with
`lie_submodule.quotient.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem lie_module_hom_ext ⦃f g : Quotientₓ N →ₗ⁅R,L⁆ M⦄ (h : f.comp (mk' N) = g.comp (mk' N)) : f = g :=
  LieModuleHom.ext$ fun x => Quotientₓ.induction_on' x$ LieModuleHom.congr_fun h

end Quotientₓ

end LieSubmodule

