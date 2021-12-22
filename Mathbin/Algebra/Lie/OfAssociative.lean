import Mathbin.Algebra.Lie.Basic
import Mathbin.Algebra.Lie.Subalgebra
import Mathbin.Algebra.Algebra.Subalgebra

/-!
# Lie algebras of associative algebras

This file defines the Lie algebra structure that arises on an associative algebra via the ring
commutator.

Since the linear endomorphisms of a Lie algebra form an associative algebra, one can define the
adjoint action as a morphism of Lie algebras from a Lie algebra to its linear endomorphisms. We
make such a definition in this file.

## Main definitions

 * `lie_algebra.of_associative_algebra`
 * `lie_algebra.of_associative_algebra_hom`
 * `lie_module.to_endomorphism`
 * `lie_algebra.ad`
 * `linear_equiv.lie_conj`
 * `alg_equiv.to_lie_equiv`

## Tags

lie algebra, ring commutator, adjoint action
-/


universe u v w w₁ w₂

section OfAssociative

variable {A : Type v} [Ringₓ A]

namespace Ringₓ

/--  The bracket operation for rings is the ring commutator, which captures the extent to which a
ring is commutative. It is identically zero exactly when the ring is commutative. -/
instance (priority := 100) : HasBracket A A :=
  ⟨fun x y => (x*y) - y*x⟩

theorem lie_def (x y : A) : ⁅x,y⁆ = (x*y) - y*x :=
  rfl

end Ringₓ

namespace LieRing

-- failed to format: format: uncaught backtrack exception
/-- An associative ring gives rise to a Lie ring by taking the bracket to be the ring commutator. -/
  instance
    ( priority := 100 )
    of_associative_ring
    : LieRing A
    where
      add_lie
          :=
          by
            simp
              only
              [
                Ringₓ.lie_def
                  ,
                  right_distrib
                  ,
                  left_distrib
                  ,
                  sub_eq_add_neg
                  ,
                  add_commₓ
                  ,
                  add_left_commₓ
                  ,
                  forall_const
                  ,
                  eq_self_iff_true
                  ,
                  neg_add_rev
                ]
        lie_add
          :=
          by
            simp
              only
              [
                Ringₓ.lie_def
                  ,
                  right_distrib
                  ,
                  left_distrib
                  ,
                  sub_eq_add_neg
                  ,
                  add_commₓ
                  ,
                  add_left_commₓ
                  ,
                  forall_const
                  ,
                  eq_self_iff_true
                  ,
                  neg_add_rev
                ]
        lie_self := by simp only [ Ringₓ.lie_def , forall_const , sub_self ]
        leibniz_lie x y z := by repeat' rw [ Ringₓ.lie_def ] noncomm_ring

theorem of_associative_ring_bracket (x y : A) : ⁅x,y⁆ = (x*y) - y*x :=
  rfl

@[simp]
theorem lie_apply {α : Type _} (f g : α → A) (a : α) : ⁅f,g⁆ a = ⁅f a,g a⁆ :=
  rfl

end LieRing

section LieAlgebra

variable {R : Type u} [CommRingₓ R] [Algebra R A]

-- failed to format: format: uncaught backtrack exception
/--
    An associative algebra gives rise to a Lie algebra by taking the bracket to be the ring
    commutator. -/
  instance
    ( priority := 100 )
    LieAlgebra.ofAssociativeAlgebra
    : LieAlgebra R A
    where
      lie_smul
        t x y
        :=
        by
          rw
            [
              LieRing.of_associative_ring_bracket
                ,
                LieRing.of_associative_ring_bracket
                ,
                Algebra.mul_smul_comm
                ,
                Algebra.smul_mul_assoc
                ,
                smul_sub
              ]

namespace AlgHom

variable {B : Type w} {C : Type w₁} [Ringₓ B] [Ringₓ C] [Algebra R B] [Algebra R C]

variable (f : A →ₐ[R] B) (g : B →ₐ[R] C)

/--  The map `of_associative_algebra` associating a Lie algebra to an associative algebra is
functorial. -/
def to_lie_hom : A →ₗ⁅R⁆ B :=
  { f.to_linear_map with
    map_lie' := fun x y =>
      show f ⁅x,y⁆ = ⁅f x,f y⁆by
        simp only [LieRing.of_associative_ring_bracket, AlgHom.map_sub, AlgHom.map_mul] }

instance : Coe (A →ₐ[R] B) (A →ₗ⁅R⁆ B) :=
  ⟨to_lie_hom⟩

@[simp]
theorem to_lie_hom_coe : f.to_lie_hom = ↑f :=
  rfl

@[simp]
theorem coe_to_lie_hom : ((f : A →ₗ⁅R⁆ B) : A → B) = f :=
  rfl

theorem to_lie_hom_apply (x : A) : f.to_lie_hom x = f x :=
  rfl

@[simp]
theorem to_lie_hom_id : (AlgHom.id R A : A →ₗ⁅R⁆ A) = LieHom.id :=
  rfl

@[simp]
theorem to_lie_hom_comp : (g.comp f : A →ₗ⁅R⁆ C) = (g : B →ₗ⁅R⁆ C).comp (f : A →ₗ⁅R⁆ B) :=
  rfl

theorem to_lie_hom_injective {f g : A →ₐ[R] B} (h : (f : A →ₗ⁅R⁆ B) = (g : A →ₗ⁅R⁆ B)) : f = g := by
  ext a
  exact LieHom.congr_fun h a

end AlgHom

end LieAlgebra

end OfAssociative

section AdjointAction

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L] [AddCommGroupₓ M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

/--  A Lie module yields a Lie algebra morphism into the linear endomorphisms of the module.

See also `lie_module.to_module_hom`. -/
@[simps]
def LieModule.toEndomorphism : L →ₗ⁅R⁆ Module.End R M :=
  { toFun := fun x => { toFun := fun m => ⁅x,m⁆, map_add' := lie_add x, map_smul' := fun t => lie_smul t x },
    map_add' := fun x y => by
      ext m
      apply add_lie,
    map_smul' := fun t x => by
      ext m
      apply smul_lie,
    map_lie' := fun x y => by
      ext m
      apply lie_lie }

/--  The adjoint action of a Lie algebra on itself. -/
def LieAlgebra.ad : L →ₗ⁅R⁆ Module.End R L :=
  LieModule.toEndomorphism R L L

@[simp]
theorem LieAlgebra.ad_apply (x y : L) : LieAlgebra.ad R L x y = ⁅x,y⁆ :=
  rfl

open LieAlgebra

theorem LieAlgebra.ad_eq_lmul_left_sub_lmul_right (A : Type v) [Ringₓ A] [Algebra R A] :
    (ad R A : A → Module.End R A) = Algebra.lmulLeft R - Algebra.lmulRight R := by
  ext a b
  simp [LieRing.of_associative_ring_bracket]

variable {R L}

theorem LieSubalgebra.ad_comp_incl_eq (K : LieSubalgebra R L) (x : K) :
    (ad R L (↑x)).comp (K.incl : K →ₗ[R] L) = (K.incl : K →ₗ[R] L).comp (ad R K x) := by
  ext y
  simp only [ad_apply, LieHom.coe_to_linear_map, LieSubalgebra.coe_incl, LinearMap.coe_comp, LieSubalgebra.coe_bracket,
    Function.comp_app]

end AdjointAction

/--  A subalgebra of an associative algebra is a Lie subalgebra of the associated Lie algebra. -/
def lieSubalgebraOfSubalgebra (R : Type u) [CommRingₓ R] (A : Type v) [Ringₓ A] [Algebra R A] (A' : Subalgebra R A) :
    LieSubalgebra R A :=
  { A'.to_submodule with
    lie_mem' := fun x y hx hy => by
      change ⁅x,y⁆ ∈ A'
      change x ∈ A' at hx
      change y ∈ A' at hy
      rw [LieRing.of_associative_ring_bracket]
      have hxy := A'.mul_mem hx hy
      have hyx := A'.mul_mem hy hx
      exact Submodule.sub_mem A'.to_submodule hxy hyx }

namespace LinearEquiv

variable {R : Type u} {M₁ : Type v} {M₂ : Type w}

variable [CommRingₓ R] [AddCommGroupₓ M₁] [Module R M₁] [AddCommGroupₓ M₂] [Module R M₂]

variable (e : M₁ ≃ₗ[R] M₂)

/--  A linear equivalence of two modules induces a Lie algebra equivalence of their endomorphisms. -/
def lie_conj : Module.End R M₁ ≃ₗ⁅R⁆ Module.End R M₂ :=
  { e.conj with
    map_lie' := fun f g =>
      show e.conj ⁅f,g⁆ = ⁅e.conj f,e.conj g⁆by
        simp only [LieRing.of_associative_ring_bracket, LinearMap.mul_eq_comp, e.conj_comp, LinearEquiv.map_sub] }

@[simp]
theorem lie_conj_apply (f : Module.End R M₁) : e.lie_conj f = e.conj f :=
  rfl

@[simp]
theorem lie_conj_symm : e.lie_conj.symm = e.symm.lie_conj :=
  rfl

end LinearEquiv

namespace AlgEquiv

variable {R : Type u} {A₁ : Type v} {A₂ : Type w}

variable [CommRingₓ R] [Ringₓ A₁] [Ringₓ A₂] [Algebra R A₁] [Algebra R A₂]

variable (e : A₁ ≃ₐ[R] A₂)

/--  An equivalence of associative algebras is an equivalence of associated Lie algebras. -/
def to_lie_equiv : A₁ ≃ₗ⁅R⁆ A₂ :=
  { e.to_linear_equiv with toFun := e.to_fun,
    map_lie' := fun x y => by
      simp [LieRing.of_associative_ring_bracket] }

@[simp]
theorem to_lie_equiv_apply (x : A₁) : e.to_lie_equiv x = e x :=
  rfl

@[simp]
theorem to_lie_equiv_symm_apply (x : A₂) : e.to_lie_equiv.symm x = e.symm x :=
  rfl

end AlgEquiv

