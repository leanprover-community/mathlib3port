import Mathbin.Algebra.Algebra.Operations 
import Mathbin.Data.Set.UnionLift 
import Mathbin.RingTheory.Subring.Pointwise

/-!
# Subalgebras over Commutative Semiring

In this file we define `subalgebra`s and the usual operations on them (`map`, `comap'`).

More lemmas about `adjoin` can be found in `ring_theory.adjoin`.
-/


universe u u' v w

open_locale TensorProduct BigOperators

/-- A subalgebra is a sub(semi)ring that includes the range of `algebra_map`. -/
structure Subalgebra(R : Type u)(A : Type v)[CommSemiringₓ R][Semiringₓ A][Algebra R A] extends Subsemiring A :
  Type v where 
  algebra_map_mem' : ∀ r, algebraMap R A r ∈ carrier 
  zero_mem' := (algebraMap R A).map_zero ▸ algebra_map_mem' 0 
  one_mem' := (algebraMap R A).map_one ▸ algebra_map_mem' 1

/-- Reinterpret a `subalgebra` as a `subsemiring`. -/
add_decl_doc Subalgebra.toSubsemiring

namespace Subalgebra

variable{R' : Type u'}{R : Type u}{A : Type v}{B : Type w}{C : Type w}

variable[CommSemiringₓ R]

variable[Semiringₓ A][Algebra R A][Semiringₓ B][Algebra R B][Semiringₓ C][Algebra R C]

include R

instance  : SetLike (Subalgebra R A) A :=
  ⟨Subalgebra.Carrier,
    fun p q h =>
      by 
        cases p <;> cases q <;> congr⟩

@[simp]
theorem mem_carrier {s : Subalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[ext]
theorem ext {S T : Subalgebra R A} (h : ∀ (x : A), x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem mem_to_subsemiring {S : Subalgebra R A} {x} : x ∈ S.to_subsemiring ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_to_subsemiring (S : Subalgebra R A) : («expr↑ » S.to_subsemiring : Set A) = S :=
  rfl

/-- Copy of a subalgebra with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : Subalgebra R A) (s : Set A) (hs : s = «expr↑ » S) : Subalgebra R A :=
  { Carrier := s, add_mem' := hs.symm ▸ S.add_mem', mul_mem' := hs.symm ▸ S.mul_mem',
    algebra_map_mem' := hs.symm ▸ S.algebra_map_mem' }

@[simp]
theorem coe_copy (S : Subalgebra R A) (s : Set A) (hs : s = «expr↑ » S) : (S.copy s hs : Set A) = s :=
  rfl

theorem copy_eq (S : Subalgebra R A) (s : Set A) (hs : s = «expr↑ » S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable(S : Subalgebra R A)

theorem algebra_map_mem (r : R) : algebraMap R A r ∈ S :=
  S.algebra_map_mem' r

theorem srange_le : (algebraMap R A).srange ≤ S.to_subsemiring :=
  fun x ⟨r, hr⟩ => hr ▸ S.algebra_map_mem r

theorem range_subset : Set.Range (algebraMap R A) ⊆ S :=
  fun x ⟨r, hr⟩ => hr ▸ S.algebra_map_mem r

theorem range_le : Set.Range (algebraMap R A) ≤ S :=
  S.range_subset

theorem one_mem : (1 : A) ∈ S :=
  S.to_subsemiring.one_mem

theorem mul_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : (x*y) ∈ S :=
  S.to_subsemiring.mul_mem hx hy

theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
  (Algebra.smul_def r x).symm ▸ S.mul_mem (S.algebra_map_mem r) hx

theorem pow_mem {x : A} (hx : x ∈ S) (n : ℕ) : x ^ n ∈ S :=
  S.to_subsemiring.pow_mem hx n

theorem zero_mem : (0 : A) ∈ S :=
  S.to_subsemiring.zero_mem

theorem add_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : (x+y) ∈ S :=
  S.to_subsemiring.add_mem hx hy

theorem neg_mem {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A) {x : A}
  (hx : x ∈ S) : -x ∈ S :=
  neg_one_smul R x ▸ S.smul_mem hx _

theorem sub_mem {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A) {x y : A}
  (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
  by 
    simpa only [sub_eq_add_neg] using S.add_mem hx (S.neg_mem hy)

theorem nsmul_mem {x : A} (hx : x ∈ S) (n : ℕ) : n • x ∈ S :=
  S.to_subsemiring.nsmul_mem hx n

theorem zsmul_mem {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A) {x : A}
  (hx : x ∈ S) : ∀ (n : ℤ), n • x ∈ S
| (n : ℕ) =>
  by 
    rw [coe_nat_zsmul]
    exact S.nsmul_mem hx n
| -[1+ n] =>
  by 
    rw [zsmul_neg_succ_of_nat]
    exact S.neg_mem (S.nsmul_mem hx _)

theorem coe_nat_mem (n : ℕ) : (n : A) ∈ S :=
  S.to_subsemiring.coe_nat_mem n

theorem coe_int_mem {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A) (n : ℤ) :
  (n : A) ∈ S :=
  Int.casesOn n (fun i => S.coe_nat_mem i) fun i => S.neg_mem$ S.coe_nat_mem$ i+1

theorem list_prod_mem {L : List A} (h : ∀ x (_ : x ∈ L), x ∈ S) : L.prod ∈ S :=
  S.to_subsemiring.list_prod_mem h

theorem list_sum_mem {L : List A} (h : ∀ x (_ : x ∈ L), x ∈ S) : L.sum ∈ S :=
  S.to_subsemiring.list_sum_mem h

theorem multiset_prod_mem {R : Type u} {A : Type v} [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A]
  (S : Subalgebra R A) {m : Multiset A} (h : ∀ x (_ : x ∈ m), x ∈ S) : m.prod ∈ S :=
  S.to_subsemiring.multiset_prod_mem m h

theorem multiset_sum_mem {m : Multiset A} (h : ∀ x (_ : x ∈ m), x ∈ S) : m.sum ∈ S :=
  S.to_subsemiring.multiset_sum_mem m h

theorem prod_mem {R : Type u} {A : Type v} [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A] (S : Subalgebra R A)
  {ι : Type w} {t : Finset ι} {f : ι → A} (h : ∀ x (_ : x ∈ t), f x ∈ S) : (∏x in t, f x) ∈ S :=
  S.to_subsemiring.prod_mem h

theorem sum_mem {ι : Type w} {t : Finset ι} {f : ι → A} (h : ∀ x (_ : x ∈ t), f x ∈ S) : (∑x in t, f x) ∈ S :=
  S.to_subsemiring.sum_mem h

/-- The projection from a subalgebra of `A` to an additive submonoid of `A`. -/
def to_add_submonoid {R : Type u} {A : Type v} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] (S : Subalgebra R A) :
  AddSubmonoid A :=
  S.to_subsemiring.to_add_submonoid

/-- The projection from a subalgebra of `A` to a submonoid of `A`. -/
def to_submonoid {R : Type u} {A : Type v} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] (S : Subalgebra R A) :
  Submonoid A :=
  S.to_subsemiring.to_submonoid

/-- A subalgebra over a ring is also a `subring`. -/
def to_subring {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A) : Subring A :=
  { S.to_subsemiring with neg_mem' := fun _ => S.neg_mem }

@[simp]
theorem mem_to_subring {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] {S : Subalgebra R A} {x} :
  x ∈ S.to_subring ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_to_subring {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A) :
  («expr↑ » S.to_subring : Set A) = S :=
  rfl

instance  : Inhabited S :=
  ⟨(0 : S.to_subsemiring)⟩

section 

/-! `subalgebra`s inherit structure from their `subsemiring` / `semiring` coercions. -/


instance to_semiring {R A} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] (S : Subalgebra R A) : Semiringₓ S :=
  S.to_subsemiring.to_semiring

instance to_comm_semiring {R A} [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A] (S : Subalgebra R A) :
  CommSemiringₓ S :=
  S.to_subsemiring.to_comm_semiring

instance to_ring {R A} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A) : Ringₓ S :=
  S.to_subring.to_ring

instance to_comm_ring {R A} [CommRingₓ R] [CommRingₓ A] [Algebra R A] (S : Subalgebra R A) : CommRingₓ S :=
  S.to_subring.to_comm_ring

instance to_ordered_semiring {R A} [CommSemiringₓ R] [OrderedSemiring A] [Algebra R A] (S : Subalgebra R A) :
  OrderedSemiring S :=
  S.to_subsemiring.to_ordered_semiring

instance to_ordered_comm_semiring {R A} [CommSemiringₓ R] [OrderedCommSemiring A] [Algebra R A] (S : Subalgebra R A) :
  OrderedCommSemiring S :=
  S.to_subsemiring.to_ordered_comm_semiring

instance to_ordered_ring {R A} [CommRingₓ R] [OrderedRing A] [Algebra R A] (S : Subalgebra R A) : OrderedRing S :=
  S.to_subring.to_ordered_ring

instance to_ordered_comm_ring {R A} [CommRingₓ R] [OrderedCommRing A] [Algebra R A] (S : Subalgebra R A) :
  OrderedCommRing S :=
  S.to_subring.to_ordered_comm_ring

instance to_linear_ordered_semiring {R A} [CommSemiringₓ R] [LinearOrderedSemiring A] [Algebra R A]
  (S : Subalgebra R A) : LinearOrderedSemiring S :=
  S.to_subsemiring.to_linear_ordered_semiring

/-! There is no `linear_ordered_comm_semiring`. -/


instance to_linear_ordered_ring {R A} [CommRingₓ R] [LinearOrderedRing A] [Algebra R A] (S : Subalgebra R A) :
  LinearOrderedRing S :=
  S.to_subring.to_linear_ordered_ring

instance to_linear_ordered_comm_ring {R A} [CommRingₓ R] [LinearOrderedCommRing A] [Algebra R A] (S : Subalgebra R A) :
  LinearOrderedCommRing S :=
  S.to_subring.to_linear_ordered_comm_ring

end 

/-- Convert a `subalgebra` to `submodule` -/
def to_submodule : Submodule R A :=
  { Carrier := S, zero_mem' := (0 : S).2, add_mem' := fun x y hx hy => (⟨x, hx⟩+⟨y, hy⟩ : S).2,
    smul_mem' := fun c x hx => (Algebra.smul_def c x).symm ▸ (⟨algebraMap R A c, S.range_le ⟨c, rfl⟩⟩*⟨x, hx⟩ : S).2 }

@[simp]
theorem mem_to_submodule {x} : x ∈ S.to_submodule ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_to_submodule (S : Subalgebra R A) : («expr↑ » S.to_submodule : Set A) = S :=
  rfl

theorem to_submodule_injective : Function.Injective (to_submodule : Subalgebra R A → Submodule R A) :=
  fun S T h =>
    ext$
      fun x =>
        by 
          rw [←mem_to_submodule, ←mem_to_submodule, h]

theorem to_submodule_inj {S U : Subalgebra R A} : S.to_submodule = U.to_submodule ↔ S = U :=
  to_submodule_injective.eq_iff

section 

/-! `subalgebra`s inherit structure from their `submodule` coercions. -/


instance module' [Semiringₓ R'] [HasScalar R' R] [Module R' A] [IsScalarTower R' R A] : Module R' S :=
  S.to_submodule.module'

instance  : Module R S :=
  S.module'

instance  [Semiringₓ R'] [HasScalar R' R] [Module R' A] [IsScalarTower R' R A] : IsScalarTower R' R S :=
  S.to_submodule.is_scalar_tower

instance algebra' [CommSemiringₓ R'] [HasScalar R' R] [Algebra R' A] [IsScalarTower R' R A] : Algebra R' S :=
  { (algebraMap R' A).codSrestrict S.to_subsemiring$
      fun x =>
        by 
          rw [Algebra.algebra_map_eq_smul_one, ←smul_one_smul R x (1 : A), ←Algebra.algebra_map_eq_smul_one]
          exact algebra_map_mem S _ with
    commutes' := fun c x => Subtype.eq$ Algebra.commutes _ _, smul_def' := fun c x => Subtype.eq$ Algebra.smul_def _ _ }

instance  : Algebra R S :=
  S.algebra'

end 

instance Nontrivial [Nontrivial A] : Nontrivial S :=
  S.to_subsemiring.nontrivial

instance no_zero_smul_divisors_bot [NoZeroSmulDivisors R A] : NoZeroSmulDivisors R S :=
  ⟨fun c x h =>
      have  : c = 0 ∨ (x : A) = 0 := eq_zero_or_eq_zero_of_smul_eq_zero (congr_argₓ coeₓ h)
      this.imp_right (@Subtype.ext_iff _ _ x 0).mpr⟩

@[simp, normCast]
theorem coe_add (x y : S) : («expr↑ » (x+y) : A) = «expr↑ » x+«expr↑ » y :=
  rfl

@[simp, normCast]
theorem coe_mul (x y : S) : («expr↑ » (x*y) : A) = «expr↑ » x*«expr↑ » y :=
  rfl

@[simp, normCast]
theorem coe_zero : ((0 : S) : A) = 0 :=
  rfl

@[simp, normCast]
theorem coe_one : ((1 : S) : A) = 1 :=
  rfl

@[simp, normCast]
theorem coe_neg {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] {S : Subalgebra R A} (x : S) :
  («expr↑ » (-x) : A) = -«expr↑ » x :=
  rfl

@[simp, normCast]
theorem coe_sub {R : Type u} {A : Type v} [CommRingₓ R] [Ringₓ A] [Algebra R A] {S : Subalgebra R A} (x y : S) :
  («expr↑ » (x - y) : A) = «expr↑ » x - «expr↑ » y :=
  rfl

@[simp, normCast]
theorem coe_smul [Semiringₓ R'] [HasScalar R' R] [Module R' A] [IsScalarTower R' R A] (r : R') (x : S) :
  («expr↑ » (r • x) : A) = r • «expr↑ » x :=
  rfl

@[simp, normCast]
theorem coe_algebra_map [CommSemiringₓ R'] [HasScalar R' R] [Algebra R' A] [IsScalarTower R' R A] (r : R') :
  «expr↑ » (algebraMap R' S r) = algebraMap R' A r :=
  rfl

@[simp, normCast]
theorem coe_pow (x : S) (n : ℕ) : («expr↑ » (x ^ n) : A) = «expr↑ » x ^ n :=
  by 
    induction' n with n ih
    ·
      simp 
    ·
      simp [pow_succₓ, ih]

@[simp, normCast]
theorem coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
  (Subtype.ext_iff.symm : (x : A) = (0 : S) ↔ x = 0)

@[simp, normCast]
theorem coe_eq_one {x : S} : (x : A) = 1 ↔ x = 1 :=
  (Subtype.ext_iff.symm : (x : A) = (1 : S) ↔ x = 1)

/-- Embedding of a subalgebra into the algebra. -/
def val : S →ₐ[R] A :=
  by 
    refineStruct { toFun := (coeₓ : S → A) } <;> intros  <;> rfl

@[simp]
theorem coe_val : (S.val : S → A) = coeₓ :=
  rfl

theorem val_apply (x : S) : S.val x = (x : A) :=
  rfl

@[simp]
theorem to_subsemiring_subtype : S.to_subsemiring.subtype = (S.val : S →+* A) :=
  rfl

@[simp]
theorem to_subring_subtype {R A : Type _} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subalgebra R A) :
  S.to_subring.subtype = (S.val : S →+* A) :=
  rfl

/-- As submodules, subalgebras are idempotent. -/
@[simp]
theorem mul_self : (S.to_submodule*S.to_submodule) = S.to_submodule :=
  by 
    apply le_antisymmₓ
    ·
      rw [Submodule.mul_le]
      intro y hy z hz 
      exact mul_mem S hy hz
    ·
      intro x hx1 
      rw [←mul_oneₓ x]
      exact Submodule.mul_mem_mul hx1 (one_mem S)

/-- Linear equivalence between `S : submodule R A` and `S`. Though these types are equal,
we define it as a `linear_equiv` to avoid type equalities. -/
def to_submodule_equiv (S : Subalgebra R A) : S.to_submodule ≃ₗ[R] S :=
  LinearEquiv.ofEq _ _ rfl

/-- Transport a subalgebra via an algebra homomorphism. -/
def map (S : Subalgebra R A) (f : A →ₐ[R] B) : Subalgebra R B :=
  { S.to_subsemiring.map (f : A →+* B) with
    algebra_map_mem' := fun r => f.commutes r ▸ Set.mem_image_of_mem _ (S.algebra_map_mem r) }

theorem map_mono {S₁ S₂ : Subalgebra R A} {f : A →ₐ[R] B} : S₁ ≤ S₂ → S₁.map f ≤ S₂.map f :=
  Set.image_subset f

theorem map_injective {S₁ S₂ : Subalgebra R A} (f : A →ₐ[R] B) (hf : Function.Injective f) (ih : S₁.map f = S₂.map f) :
  S₁ = S₂ :=
  ext$ Set.ext_iff.1$ Set.image_injective.2 hf$ Set.ext$ SetLike.ext_iff.mp ih

@[simp]
theorem map_id (S : Subalgebra R A) : S.map (AlgHom.id R A) = S :=
  SetLike.coe_injective$ Set.image_id _

theorem map_map (S : Subalgebra R A) (g : B →ₐ[R] C) (f : A →ₐ[R] B) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective$ Set.image_image _ _ _

theorem mem_map {S : Subalgebra R A} {f : A →ₐ[R] B} {y : B} : y ∈ map S f ↔ ∃ (x : _)(_ : x ∈ S), f x = y :=
  Subsemiring.mem_map

/-- Preimage of a subalgebra under an algebra homomorphism. -/
def comap' (S : Subalgebra R B) (f : A →ₐ[R] B) : Subalgebra R A :=
  { S.to_subsemiring.comap (f : A →+* B) with
    algebra_map_mem' := fun r => show f (algebraMap R A r) ∈ S from (f.commutes r).symm ▸ S.algebra_map_mem r }

theorem map_le {S : Subalgebra R A} {f : A →ₐ[R] B} {U : Subalgebra R B} : map S f ≤ U ↔ S ≤ comap' U f :=
  Set.image_subset_iff

theorem gc_map_comap (f : A →ₐ[R] B) : GaloisConnection (fun S => map S f) fun S => comap' S f :=
  fun S U => map_le

@[simp]
theorem mem_comap (S : Subalgebra R B) (f : A →ₐ[R] B) (x : A) : x ∈ S.comap' f ↔ f x ∈ S :=
  Iff.rfl

@[simp, normCast]
theorem coe_comap (S : Subalgebra R B) (f : A →ₐ[R] B) : (S.comap' f : Set A) = f ⁻¹' (S : Set B) :=
  rfl

instance NoZeroDivisors {R A : Type _} [CommRingₓ R] [Semiringₓ A] [NoZeroDivisors A] [Algebra R A]
  (S : Subalgebra R A) : NoZeroDivisors S :=
  S.to_subsemiring.no_zero_divisors

instance IsDomain {R A : Type _} [CommRingₓ R] [Ringₓ A] [IsDomain A] [Algebra R A] (S : Subalgebra R A) : IsDomain S :=
  Subring.is_domain S.to_subring

end Subalgebra

namespace AlgHom

variable{R : Type u}{A : Type v}{B : Type w}

variable[CommSemiringₓ R][Semiringₓ A][Semiringₓ B][Algebra R A][Algebra R B]

variable(φ : A →ₐ[R] B)

/-- Range of an `alg_hom` as a subalgebra. -/
protected def range (φ : A →ₐ[R] B) : Subalgebra R B :=
  { φ.to_ring_hom.srange with algebra_map_mem' := fun r => ⟨algebraMap R A r, φ.commutes r⟩ }

@[simp]
theorem mem_range (φ : A →ₐ[R] B) {y : B} : y ∈ φ.range ↔ ∃ x, φ x = y :=
  RingHom.mem_srange

theorem mem_range_self (φ : A →ₐ[R] B) (x : A) : φ x ∈ φ.range :=
  φ.mem_range.2 ⟨x, rfl⟩

@[simp]
theorem coe_range (φ : A →ₐ[R] B) : (φ.range : Set B) = Set.Range φ :=
  by 
    ext 
    rw [SetLike.mem_coe, mem_range]
    rfl

/-- Restrict the codomain of an algebra homomorphism. -/
def cod_restrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) : A →ₐ[R] S :=
  { RingHom.codSrestrict (f : A →+* B) S.to_subsemiring hf with commutes' := fun r => Subtype.eq$ f.commutes r }

@[simp]
theorem val_comp_cod_restrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) :
  S.val.comp (f.cod_restrict S hf) = f :=
  AlgHom.ext$ fun _ => rfl

@[simp]
theorem coe_cod_restrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
  «expr↑ » (f.cod_restrict S hf x) = f x :=
  rfl

theorem injective_cod_restrict (f : A →ₐ[R] B) (S : Subalgebra R B) (hf : ∀ x, f x ∈ S) :
  Function.Injective (f.cod_restrict S hf) ↔ Function.Injective f :=
  ⟨fun H x y hxy => H$ Subtype.eq hxy, fun H x y hxy => H (congr_argₓ Subtype.val hxy : _)⟩

/-- Restrict the codomain of a alg_hom `f` to `f.range`.

This is the bundled version of `set.range_factorization`. -/
@[reducible]
def range_restrict (f : A →ₐ[R] B) : A →ₐ[R] f.range :=
  f.cod_restrict f.range f.mem_range_self

/-- The equalizer of two R-algebra homomorphisms -/
def equalizer (ϕ ψ : A →ₐ[R] B) : Subalgebra R A :=
  { Carrier := { a | ϕ a = ψ a },
    add_mem' :=
      fun x y hx hy =>
        by 
          change ϕ x = ψ x at hx 
          change ϕ y = ψ y at hy 
          change ϕ (x+y) = ψ (x+y)
          rw [AlgHom.map_add, AlgHom.map_add, hx, hy],
    mul_mem' :=
      fun x y hx hy =>
        by 
          change ϕ x = ψ x at hx 
          change ϕ y = ψ y at hy 
          change ϕ (x*y) = ψ (x*y)
          rw [AlgHom.map_mul, AlgHom.map_mul, hx, hy],
    algebra_map_mem' :=
      fun x =>
        by 
          change ϕ (algebraMap R A x) = ψ (algebraMap R A x)
          rw [AlgHom.commutes, AlgHom.commutes] }

@[simp]
theorem mem_equalizer (ϕ ψ : A →ₐ[R] B) (x : A) : x ∈ ϕ.equalizer ψ ↔ ϕ x = ψ x :=
  Iff.rfl

/-- The range of a morphism of algebras is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `subtype.fintype` if `B` is also a fintype. -/
instance fintype_range [Fintype A] [DecidableEq B] (φ : A →ₐ[R] B) : Fintype φ.range :=
  Set.fintypeRange φ

end AlgHom

namespace AlgEquiv

variable{R : Type u}{A : Type v}{B : Type w}

variable[CommSemiringₓ R][Semiringₓ A][Semiringₓ B][Algebra R A][Algebra R B]

/-- Restrict an algebra homomorphism with a left inverse to an algebra isomorphism to its range.

This is a computable alternative to `alg_equiv.of_injective`. -/
def of_left_inverse {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f) : A ≃ₐ[R] f.range :=
  { f.range_restrict with toFun := f.range_restrict, invFun := g ∘ f.range.val, left_inv := h,
    right_inv :=
      fun x =>
        Subtype.ext$
          let ⟨x', hx'⟩ := f.mem_range.mp x.prop 
          show f (g x) = x by 
            rw [←hx', h x'] }

@[simp]
theorem of_left_inverse_apply {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f) (x : A) :
  «expr↑ » (of_left_inverse h x) = f x :=
  rfl

@[simp]
theorem of_left_inverse_symm_apply {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f) (x : f.range) :
  (of_left_inverse h).symm x = g x :=
  rfl

/-- Restrict an injective algebra homomorphism to an algebra isomorphism -/
noncomputable def of_injective (f : A →ₐ[R] B) (hf : Function.Injective f) : A ≃ₐ[R] f.range :=
  of_left_inverse (Classical.some_spec hf.has_left_inverse)

@[simp]
theorem of_injective_apply (f : A →ₐ[R] B) (hf : Function.Injective f) (x : A) : «expr↑ » (of_injective f hf x) = f x :=
  rfl

/-- Restrict an algebra homomorphism between fields to an algebra isomorphism -/
noncomputable def of_injective_field {E F : Type _} [DivisionRing E] [Semiringₓ F] [Nontrivial F] [Algebra R E]
  [Algebra R F] (f : E →ₐ[R] F) : E ≃ₐ[R] f.range :=
  of_injective f f.to_ring_hom.injective

end AlgEquiv

namespace Algebra

variable(R : Type u){A : Type v}{B : Type w}

variable[CommSemiringₓ R][Semiringₓ A][Algebra R A][Semiringₓ B][Algebra R B]

/-- The minimal subalgebra that includes `s`. -/
def adjoin (s : Set A) : Subalgebra R A :=
  { Subsemiring.closure (Set.Range (algebraMap R A) ∪ s) with
    algebra_map_mem' := fun r => Subsemiring.subset_closure$ Or.inl ⟨r, rfl⟩ }

variable{R}

protected theorem gc : GaloisConnection (adjoin R : Set A → Subalgebra R A) coeₓ :=
  fun s S =>
    ⟨fun H => le_transₓ (le_transₓ (Set.subset_union_right _ _) Subsemiring.subset_closure) H,
      fun H =>
        show Subsemiring.closure (Set.Range (algebraMap R A) ∪ s) ≤ S.to_subsemiring from
          Subsemiring.closure_le.2$ Set.union_subset S.range_subset H⟩

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : GaloisInsertion (adjoin R : Set A → Subalgebra R A) coeₓ :=
  { choice := fun s hs => (adjoin R s).copy s$ le_antisymmₓ (Algebra.gc.le_u_l s) hs, gc := Algebra.gc,
    le_l_u := fun S => (Algebra.gc (S : Set A) (adjoin R S)).1$ le_reflₓ _,
    choice_eq := fun _ _ => Subalgebra.copy_eq _ _ _ }

instance  : CompleteLattice (Subalgebra R A) :=
  GaloisInsertion.liftCompleteLattice Algebra.gi

@[simp]
theorem coe_top : («expr↑ » (⊤ : Subalgebra R A) : Set A) = Set.Univ :=
  rfl

@[simp]
theorem mem_top {x : A} : x ∈ (⊤ : Subalgebra R A) :=
  Set.mem_univ x

@[simp]
theorem top_to_submodule : (⊤ : Subalgebra R A).toSubmodule = ⊤ :=
  rfl

@[simp]
theorem top_to_subsemiring : (⊤ : Subalgebra R A).toSubsemiring = ⊤ :=
  rfl

@[simp, normCast]
theorem coe_inf (S T : Subalgebra R A) : («expr↑ » (S⊓T) : Set A) = S ∩ T :=
  rfl

@[simp]
theorem mem_inf {S T : Subalgebra R A} {x : A} : x ∈ S⊓T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

@[simp]
theorem inf_to_submodule (S T : Subalgebra R A) : (S⊓T).toSubmodule = S.to_submodule⊓T.to_submodule :=
  rfl

@[simp]
theorem inf_to_subsemiring (S T : Subalgebra R A) : (S⊓T).toSubsemiring = S.to_subsemiring⊓T.to_subsemiring :=
  rfl

@[simp, normCast]
theorem coe_Inf (S : Set (Subalgebra R A)) : («expr↑ » (Inf S) : Set A) = ⋂(s : _)(_ : s ∈ S), «expr↑ » s :=
  Inf_image

theorem mem_Inf {S : Set (Subalgebra R A)} {x : A} : x ∈ Inf S ↔ ∀ p (_ : p ∈ S), x ∈ p :=
  by 
    simp only [←SetLike.mem_coe, coe_Inf, Set.mem_bInter_iff]

@[simp]
theorem Inf_to_submodule (S : Set (Subalgebra R A)) : (Inf S).toSubmodule = Inf (Subalgebra.toSubmodule '' S) :=
  SetLike.coe_injective$
    by 
      simp 

@[simp]
theorem Inf_to_subsemiring (S : Set (Subalgebra R A)) : (Inf S).toSubsemiring = Inf (Subalgebra.toSubsemiring '' S) :=
  SetLike.coe_injective$
    by 
      simp 

@[simp, normCast]
theorem coe_infi {ι : Sort _} {S : ι → Subalgebra R A} : («expr↑ » (⨅i, S i) : Set A) = ⋂i, S i :=
  by 
    simp [infi]

theorem mem_infi {ι : Sort _} {S : ι → Subalgebra R A} {x : A} : (x ∈ ⨅i, S i) ↔ ∀ i, x ∈ S i :=
  by 
    simp only [infi, mem_Inf, Set.forall_range_iff]

@[simp]
theorem infi_to_submodule {ι : Sort _} (S : ι → Subalgebra R A) : (⨅i, S i).toSubmodule = ⨅i, (S i).toSubmodule :=
  SetLike.coe_injective$
    by 
      simp 

instance  : Inhabited (Subalgebra R A) :=
  ⟨⊥⟩

theorem mem_bot {x : A} : x ∈ (⊥ : Subalgebra R A) ↔ x ∈ Set.Range (algebraMap R A) :=
  suffices (of_id R A).range = (⊥ : Subalgebra R A)by 
    rw [←this, ←SetLike.mem_coe, AlgHom.coe_range]
    rfl 
  le_bot_iff.mp fun x hx => Subalgebra.range_le _ ((of_id R A).coe_range ▸ hx)

theorem to_submodule_bot : (⊥ : Subalgebra R A).toSubmodule = R∙1 :=
  by 
    ext x 
    simp [mem_bot, -Set.singleton_one, Submodule.mem_span_singleton, Algebra.smul_def]

@[simp]
theorem coe_bot : ((⊥ : Subalgebra R A) : Set A) = Set.Range (algebraMap R A) :=
  by 
    simp [Set.ext_iff, Algebra.mem_bot]

theorem eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ ∀ (x : A), x ∈ S :=
  ⟨fun h x =>
      by 
        rw [h] <;> exact mem_top,
    fun h =>
      by 
        ext x <;> exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

@[simp]
theorem map_top (f : A →ₐ[R] B) : Subalgebra.map (⊤ : Subalgebra R A) f = f.range :=
  Subalgebra.ext$ fun x => ⟨fun ⟨y, _, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, Algebra.mem_top, hy⟩⟩

@[simp]
theorem map_bot (f : A →ₐ[R] B) : Subalgebra.map (⊥ : Subalgebra R A) f = ⊥ :=
  eq_bot_iff.2$
    fun x ⟨y, hy, hfy⟩ =>
      let ⟨r, hr⟩ := mem_bot.1 hy 
      Subalgebra.range_le _
        ⟨r,
          by 
            rwa [←f.commutes, hr]⟩

@[simp]
theorem comap_top (f : A →ₐ[R] B) : Subalgebra.comap' (⊤ : Subalgebra R B) f = ⊤ :=
  eq_top_iff.2$ fun x => mem_top

/-- `alg_hom` to `⊤ : subalgebra R A`. -/
def to_top : A →ₐ[R] (⊤ : Subalgebra R A) :=
  (AlgHom.id R A).codRestrict ⊤ fun _ => mem_top

theorem surjective_algebra_map_iff : Function.Surjective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ :=
  ⟨fun h =>
      eq_bot_iff.2$
        fun y _ =>
          let ⟨x, hx⟩ := h y 
          hx ▸ Subalgebra.algebra_map_mem _ _,
    fun h y => Algebra.mem_bot.1$ eq_bot_iff.1 h (Algebra.mem_top : y ∈ _)⟩

theorem bijective_algebra_map_iff {R A : Type _} [Field R] [Semiringₓ A] [Nontrivial A] [Algebra R A] :
  Function.Bijective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ :=
  ⟨fun h => surjective_algebra_map_iff.1 h.2, fun h => ⟨(algebraMap R A).Injective, surjective_algebra_map_iff.2 h⟩⟩

/-- The bottom subalgebra is isomorphic to the base ring. -/
noncomputable def bot_equiv_of_injective (h : Function.Injective (algebraMap R A)) : (⊥ : Subalgebra R A) ≃ₐ[R] R :=
  AlgEquiv.symm$
    AlgEquiv.ofBijective (Algebra.ofId R _)
      ⟨fun x y hxy => h (congr_argₓ Subtype.val hxy : _),
        fun ⟨y, hy⟩ =>
          let ⟨x, hx⟩ := Algebra.mem_bot.1 hy
          ⟨x, Subtype.eq hx⟩⟩

/-- The bottom subalgebra is isomorphic to the field. -/
noncomputable def bot_equiv (F R : Type _) [Field F] [Semiringₓ R] [Nontrivial R] [Algebra F R] :
  (⊥ : Subalgebra F R) ≃ₐ[F] F :=
  bot_equiv_of_injective (RingHom.injective _)

/-- The top subalgebra is isomorphic to the field. -/
noncomputable def top_equiv : (⊤ : Subalgebra R A) ≃ₐ[R] A :=
  (AlgEquiv.ofBijective to_top
      ⟨fun _ _ => Subtype.mk.injₓ,
        fun x =>
          ⟨x.val,
            by 
              ext 
              rfl⟩⟩ :
    A ≃ₐ[R] (⊤ : Subalgebra R A)).symm

end Algebra

namespace Subalgebra

open Algebra

variable{R : Type u}{A : Type v}{B : Type w}

variable[CommSemiringₓ R][Semiringₓ A][Algebra R A][Semiringₓ B][Algebra R B]

variable(S : Subalgebra R A)

theorem subsingleton_of_subsingleton [Subsingleton A] : Subsingleton (Subalgebra R A) :=
  ⟨fun B C =>
      ext
        fun x =>
          by 
            simp only [Subsingleton.elimₓ x 0, zero_mem]⟩

/--
For performance reasons this is not an instance. If you need this instance, add
```
local attribute [instance] alg_hom.subsingleton subalgebra.subsingleton_of_subsingleton
```
in the section that needs it.
-/
theorem _root_.alg_hom.subsingleton [Subsingleton (Subalgebra R A)] : Subsingleton (A →ₐ[R] B) :=
  ⟨fun f g =>
      AlgHom.ext$
        fun a =>
          have  : a ∈ (⊥ : Subalgebra R A) := Subsingleton.elimₓ (⊤ : Subalgebra R A) ⊥ ▸ mem_top 
          let ⟨x, hx⟩ := Set.mem_range.mp (mem_bot.mp this)
          hx ▸ (f.commutes _).trans (g.commutes _).symm⟩

-- error in Algebra.Algebra.Subalgebra: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem _root_.alg_equiv.subsingleton_left [subsingleton (subalgebra R A)] : subsingleton «expr ≃ₐ[ ] »(A, R, B) :=
begin
  haveI [] [":", expr subsingleton «expr →ₐ[ ] »(A, R, B)] [":=", expr alg_hom.subsingleton],
  exact [expr ⟨λ f g, alg_equiv.ext (λ x, alg_hom.ext_iff.mp (subsingleton.elim f.to_alg_hom g.to_alg_hom) x)⟩]
end

-- error in Algebra.Algebra.Subalgebra: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem _root_.alg_equiv.subsingleton_right [subsingleton (subalgebra R B)] : subsingleton «expr ≃ₐ[ ] »(A, R, B) :=
begin
  haveI [] [":", expr subsingleton «expr ≃ₐ[ ] »(B, R, A)] [":=", expr alg_equiv.subsingleton_left],
  exact [expr ⟨λ
    f
    g, eq.trans (alg_equiv.symm_symm _).symm (by rw ["[", expr subsingleton.elim f.symm g.symm, ",", expr alg_equiv.symm_symm, "]"] [])⟩]
end

theorem range_val : S.val.range = S :=
  ext$ Set.ext_iff.1$ S.val.coe_range.trans Subtype.range_val

instance  : Unique (Subalgebra R R) :=
  { Algebra.Subalgebra.inhabited with
    uniq :=
      by 
        intro S 
        refine' le_antisymmₓ (fun r hr => _) bot_le 
        simp only [Set.mem_range, mem_bot, id.map_eq_self, exists_apply_eq_applyₓ, default] }

/-- The map `S → T` when `S` is a subalgebra contained in the subalgebra `T`.

This is the subalgebra version of `submodule.of_le`, or `subring.inclusion`  -/
def inclusion {S T : Subalgebra R A} (h : S ≤ T) : S →ₐ[R] T :=
  { toFun := Set.inclusion h, map_one' := rfl, map_add' := fun _ _ => rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
    commutes' := fun _ => rfl }

theorem inclusion_injective {S T : Subalgebra R A} (h : S ≤ T) : Function.Injective (inclusion h) :=
  fun _ _ => Subtype.ext ∘ Subtype.mk.injₓ

@[simp]
theorem inclusion_self {S : Subalgebra R A} : inclusion (le_reflₓ S) = AlgHom.id R S :=
  AlgHom.ext$ fun x => Subtype.ext rfl

@[simp]
theorem inclusion_right {S T : Subalgebra R A} (h : S ≤ T) (x : T) (m : (x : A) ∈ S) : inclusion h ⟨x, m⟩ = x :=
  Subtype.ext rfl

@[simp]
theorem inclusion_inclusion {S T U : Subalgebra R A} (hst : S ≤ T) (htu : T ≤ U) (x : S) :
  inclusion htu (inclusion hst x) = inclusion (le_transₓ hst htu) x :=
  Subtype.ext rfl

@[simp]
theorem coe_inclusion {S T : Subalgebra R A} (h : S ≤ T) (s : S) : (inclusion h s : A) = s :=
  rfl

/-- Two subalgebras that are equal are also equivalent as algebras.

This is the `subalgebra` version of `linear_equiv.of_eq` and `equiv.set.of_eq`. -/
@[simps apply]
def equiv_of_eq (S T : Subalgebra R A) (h : S = T) : S ≃ₐ[R] T :=
  { LinearEquiv.ofEq _ _ (congr_argₓ to_submodule h) with toFun := fun x => ⟨x, h ▸ x.2⟩,
    invFun := fun x => ⟨x, h.symm ▸ x.2⟩, map_mul' := fun _ _ => rfl, commutes' := fun _ => rfl }

@[simp]
theorem equiv_of_eq_symm (S T : Subalgebra R A) (h : S = T) : (equiv_of_eq S T h).symm = equiv_of_eq T S h.symm :=
  rfl

@[simp]
theorem equiv_of_eq_rfl (S : Subalgebra R A) : equiv_of_eq S S rfl = AlgEquiv.refl :=
  by 
    ext 
    rfl

@[simp]
theorem equiv_of_eq_trans (S T U : Subalgebra R A) (hST : S = T) (hTU : T = U) :
  (equiv_of_eq S T hST).trans (equiv_of_eq T U hTU) = equiv_of_eq S U (trans hST hTU) :=
  rfl

section Prod

variable(S₁ : Subalgebra R B)

/-- The product of two subalgebras is a subalgebra. -/
def Prod : Subalgebra R (A × B) :=
  { S.to_subsemiring.prod S₁.to_subsemiring with Carrier := Set.Prod S S₁,
    algebra_map_mem' := fun r => ⟨algebra_map_mem _ _, algebra_map_mem _ _⟩ }

@[simp]
theorem coe_prod : (Prod S S₁ : Set (A × B)) = Set.Prod S S₁ :=
  rfl

theorem prod_to_submodule : (S.prod S₁).toSubmodule = S.to_submodule.prod S₁.to_submodule :=
  rfl

@[simp]
theorem mem_prod {S : Subalgebra R A} {S₁ : Subalgebra R B} {x : A × B} : x ∈ Prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ :=
  Set.mem_prod

@[simp]
theorem prod_top : (Prod ⊤ ⊤ : Subalgebra R (A × B)) = ⊤ :=
  by 
    ext <;> simp 

theorem prod_mono {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} : S ≤ T → S₁ ≤ T₁ → Prod S S₁ ≤ Prod T T₁ :=
  Set.prod_mono

@[simp]
theorem prod_inf_prod {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} : S.prod S₁⊓T.prod T₁ = (S⊓T).Prod (S₁⊓T₁) :=
  SetLike.coe_injective Set.prod_inter_prod

end Prod

section SuprLift

variable{ι : Type _}

theorem coe_supr_of_directed [Nonempty ι] {S : ι → Subalgebra R A} (dir : Directed (· ≤ ·) S) :
  «expr↑ » (supr S) = ⋃i, (S i : Set A) :=
  let K : Subalgebra R A :=
    { Carrier := ⋃i, S i,
      mul_mem' :=
        fun x y hx hy =>
          let ⟨i, hi⟩ := Set.mem_Union.1 hx 
          let ⟨j, hj⟩ := Set.mem_Union.1 hy 
          let ⟨k, hik, hjk⟩ := dir i j 
          Set.mem_Union.2 ⟨k, Subalgebra.mul_mem (S k) (hik hi) (hjk hj)⟩,
      add_mem' :=
        fun x y hx hy =>
          let ⟨i, hi⟩ := Set.mem_Union.1 hx 
          let ⟨j, hj⟩ := Set.mem_Union.1 hy 
          let ⟨k, hik, hjk⟩ := dir i j 
          Set.mem_Union.2 ⟨k, Subalgebra.add_mem (S k) (hik hi) (hjk hj)⟩,
      algebra_map_mem' :=
        fun r =>
          let i := @Nonempty.some ι inferInstance 
          Set.mem_Union.2 ⟨i, Subalgebra.algebra_map_mem _ _⟩ }
  have  : supr S = K :=
    le_antisymmₓ (supr_le fun i => Set.subset_Union (fun i => «expr↑ » (S i)) i)
      (SetLike.coe_subset_coe.1 (Set.Union_subset fun i => SetLike.coe_subset_coe.2 (le_supr _ _)))
  this.symm ▸ rfl

/-- Define an algebra homomorphism on a directed supremum of subalgebras by defining
it on each subalgebra, and proving that it agrees on the intersection of subalgebras. -/
noncomputable def supr_lift [Nonempty ι] (K : ι → Subalgebra R A) (dir : Directed (· ≤ ·) K) (f : ∀ i, K i →ₐ[R] B)
  (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)) (T : Subalgebra R A) (hT : T = supr K) :
  «expr↥ » T →ₐ[R] B :=
  by 
    subst hT <;>
      exact
        { toFun :=
            Set.unionLift (fun i => «expr↑ » (K i)) (fun i x => f i x)
              (fun i j x hxi hxj =>
                let ⟨k, hik, hjk⟩ := dir i j 
                by 
                  rw [hf i k hik, hf j k hjk]
                  rfl)
              («expr↑ » (supr K))
              (by 
                rw [coe_supr_of_directed dir] <;> rfl),
          map_one' :=
            Set.Union_lift_const _ (fun _ => 1) (fun _ => rfl) _
              (by 
                simp ),
          map_zero' :=
            Set.Union_lift_const _ (fun _ => 0) (fun _ => rfl) _
              (by 
                simp ),
          map_mul' :=
            Set.Union_lift_binary (coe_supr_of_directed dir) dir _ (fun _ => ·*·) (fun _ _ _ => rfl) _
              (by 
                simp ),
          map_add' :=
            Set.Union_lift_binary (coe_supr_of_directed dir) dir _ (fun _ => ·+·) (fun _ _ _ => rfl) _
              (by 
                simp ),
          commutes' :=
            fun r =>
              Set.Union_lift_const _ (fun _ => algebraMap _ _ r) (fun _ => rfl) _
                fun i =>
                  by 
                    erw [AlgHom.commutes (f i)] }

variable[Nonempty
      ι]{K :
    ι →
      Subalgebra R
        A}{dir :
    Directed (· ≤ ·)
      K}{f :
    ∀ i,
      K i →ₐ[R]
        B}{hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}{T : Subalgebra R A}{hT : T = supr K}

@[simp]
theorem supr_lift_inclusion {i : ι} (x : K i) (h : K i ≤ T) : supr_lift K dir f hf T hT (inclusion h x) = f i x :=
  by 
    subst T <;> exact Set.Union_lift_inclusion _ _

@[simp]
theorem supr_lift_comp_inclusion {i : ι} (h : K i ≤ T) : (supr_lift K dir f hf T hT).comp (inclusion h) = f i :=
  by 
    ext <;> simp 

@[simp]
theorem supr_lift_mk {i : ι} (x : K i) (hx : (x : A) ∈ T) : supr_lift K dir f hf T hT ⟨x, hx⟩ = f i x :=
  by 
    subst hT <;> exact Set.Union_lift_mk x hx

theorem supr_lift_of_mem {i : ι} (x : T) (hx : (x : A) ∈ K i) : supr_lift K dir f hf T hT x = f i ⟨x, hx⟩ :=
  by 
    subst hT <;> exact Set.Union_lift_of_mem x hx

end SuprLift

/-! ## Actions by `subalgebra`s

These are just copies of the definitions about `subsemiring` starting from
`subring.mul_action`.
-/


section Actions

variable{α β : Type _}

/-- The action by a subalgebra is the action by the underlying ring. -/
instance  [MulAction A α] (S : Subalgebra R A) : MulAction S α :=
  S.to_subsemiring.mul_action

theorem smul_def [MulAction A α] {S : Subalgebra R A} (g : S) (m : α) : g • m = (g : A) • m :=
  rfl

instance smul_comm_class_left [MulAction A β] [HasScalar α β] [SmulCommClass A α β] (S : Subalgebra R A) :
  SmulCommClass S α β :=
  S.to_subsemiring.smul_comm_class_left

instance smul_comm_class_right [HasScalar α β] [MulAction A β] [SmulCommClass α A β] (S : Subalgebra R A) :
  SmulCommClass α S β :=
  S.to_subsemiring.smul_comm_class_right

/-- Note that this provides `is_scalar_tower S R R` which is needed by `smul_mul_assoc`. -/
instance is_scalar_tower_left [HasScalar α β] [MulAction A α] [MulAction A β] [IsScalarTower A α β]
  (S : Subalgebra R A) : IsScalarTower S α β :=
  S.to_subsemiring.is_scalar_tower

instance  [MulAction A α] [HasFaithfulScalar A α] (S : Subalgebra R A) : HasFaithfulScalar S α :=
  S.to_subsemiring.has_faithful_scalar

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance  [AddMonoidₓ α] [DistribMulAction A α] (S : Subalgebra R A) : DistribMulAction S α :=
  S.to_subsemiring.distrib_mul_action

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance module_left [AddCommMonoidₓ α] [Module A α] (S : Subalgebra R A) : Module S α :=
  S.to_subsemiring.module

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance to_algebra {R A : Type _} [CommSemiringₓ R] [CommSemiringₓ A] [Semiringₓ α] [Algebra R A] [Algebra A α]
  (S : Subalgebra R A) : Algebra S α :=
  Algebra.ofSubsemiring S.to_subsemiring

theorem algebra_map_eq {R A : Type _} [CommSemiringₓ R] [CommSemiringₓ A] [Semiringₓ α] [Algebra R A] [Algebra A α]
  (S : Subalgebra R A) : algebraMap S α = (algebraMap A α).comp S.val :=
  rfl

@[simp]
theorem srange_algebra_map {R A : Type _} [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A] (S : Subalgebra R A) :
  (algebraMap S A).srange = S.to_subsemiring :=
  by 
    rw [algebra_map_eq, Algebra.id.map_eq_id, RingHom.id_comp, ←to_subsemiring_subtype, Subsemiring.srange_subtype]

@[simp]
theorem range_algebra_map {R A : Type _} [CommRingₓ R] [CommRingₓ A] [Algebra R A] (S : Subalgebra R A) :
  (algebraMap S A).range = S.to_subring :=
  by 
    rw [algebra_map_eq, Algebra.id.map_eq_id, RingHom.id_comp, ←to_subring_subtype, Subring.range_subtype]

instance no_zero_smul_divisors_top [NoZeroDivisors A] (S : Subalgebra R A) : NoZeroSmulDivisors S A :=
  ⟨fun c x h =>
      have  : (c : A) = 0 ∨ x = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h 
      this.imp_left (@Subtype.ext_iff _ _ c 0).mpr⟩

end Actions

section Pointwise

variable{R' : Type _}[Semiringₓ R'][MulSemiringAction R' A][SmulCommClass R' R A]

/-- The action on a subalgebra corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : MulAction R' (Subalgebra R A) :=
  { smul := fun a S => S.map (MulSemiringAction.toAlgHom _ _ a),
    one_smul :=
      fun S =>
        (congr_argₓ (fun f => S.map f)
              (AlgHom.ext$
                by 
                  exact one_smul R')).trans
          S.map_id,
    mul_smul :=
      fun a₁ a₂ S =>
        (congr_argₓ (fun f => S.map f)
              (AlgHom.ext$
                by 
                  exact mul_smul _ _)).trans
          (S.map_map _ _).symm }

localized [Pointwise] attribute [instance] Subalgebra.pointwiseMulAction

open_locale Pointwise

@[simp]
theorem coe_pointwise_smul (m : R') (S : Subalgebra R A) : «expr↑ » (m • S) = m • (S : Set A) :=
  rfl

@[simp]
theorem pointwise_smul_to_subsemiring (m : R') (S : Subalgebra R A) : (m • S).toSubsemiring = m • S.to_subsemiring :=
  rfl

@[simp]
theorem pointwise_smul_to_submodule (m : R') (S : Subalgebra R A) : (m • S).toSubmodule = m • S.to_submodule :=
  rfl

@[simp]
theorem pointwise_smul_to_subring {R' R A : Type _} [Semiringₓ R'] [CommRingₓ R] [Ringₓ A] [MulSemiringAction R' A]
  [Algebra R A] [SmulCommClass R' R A] (m : R') (S : Subalgebra R A) : (m • S).toSubring = m • S.to_subring :=
  rfl

theorem smul_mem_pointwise_smul (m : R') (r : A) (S : Subalgebra R A) : r ∈ S → m • r ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set A))

end Pointwise

end Subalgebra

section Nat

variable{R : Type _}[Semiringₓ R]

/-- A subsemiring is a `ℕ`-subalgebra. -/
def subalgebraOfSubsemiring (S : Subsemiring R) : Subalgebra ℕ R :=
  { S with algebra_map_mem' := fun i => S.coe_nat_mem i }

@[simp]
theorem mem_subalgebra_of_subsemiring {x : R} {S : Subsemiring R} : x ∈ subalgebraOfSubsemiring S ↔ x ∈ S :=
  Iff.rfl

end Nat

section Int

variable{R : Type _}[Ringₓ R]

/-- A subring is a `ℤ`-subalgebra. -/
def subalgebraOfSubring (S : Subring R) : Subalgebra ℤ R :=
  { S with
    algebra_map_mem' :=
      fun i =>
        Int.induction_on i S.zero_mem (fun i ih => S.add_mem ih S.one_mem)
          fun i ih =>
            show ((-i - 1 : ℤ) : R) ∈ S by 
              rw [Int.cast_sub, Int.cast_one]
              exact S.sub_mem ih S.one_mem }

variable{S : Type _}[Semiringₓ S]

@[simp]
theorem mem_subalgebra_of_subring {x : R} {S : Subring R} : x ∈ subalgebraOfSubring S ↔ x ∈ S :=
  Iff.rfl

end Int

