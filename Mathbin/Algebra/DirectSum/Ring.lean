import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.Algebra.GradedMonoid
import Mathbin.Algebra.DirectSum.Basic
import Mathbin.Algebra.BigOperators.Pi

/-!
# Additively-graded multiplicative structures on `⨁ i, A i`

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over `⨁ i, A i` such that `(*) : A i → A j → A (i + j)`; that is to say, `A` forms an
additively-graded ring. The typeclasses are:

* `direct_sum.gnon_unital_non_assoc_semiring A`
* `direct_sum.gsemiring A`
* `direct_sum.gcomm_semiring A`

Respectively, these imbue the external direct sum `⨁ i, A i` with:

* `direct_sum.non_unital_non_assoc_semiring`
* `direct_sum.semiring`, `direct_sum.ring`
* `direct_sum.comm_semiring`, `direct_sum.comm_ring`

the base ring `A 0` with:

* `direct_sum.grade_zero.non_unital_non_assoc_semiring`
* `direct_sum.grade_zero.semiring`, `direct_sum.grade_zero.ring`
* `direct_sum.grade_zero.comm_semiring`, `direct_sum.grade_zero.comm_ring`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* `direct_sum.grade_zero.has_scalar (A 0)`, `direct_sum.grade_zero.smul_with_zero (A 0)`
* `direct_sum.grade_zero.module (A 0)`
* (nothing)

Note that in the presence of these instances, `⨁ i, A i` itself inherits an `A 0`-action.

`direct_sum.of_zero_ring_hom : A 0 →+* ⨁ i, A i` provides `direct_sum.of A 0` as a ring
homomorphism.

`direct_sum.to_semiring` extends `direct_sum.to_add_monoid` to produce a `ring_hom`.

## Direct sums of subobjects

Additionally, this module provides helper functions to construct `gsemiring` and `gcomm_semiring`
instances for:

* `A : ι → submonoid S`:
  `direct_sum.gsemiring.of_add_submonoids`, `direct_sum.gcomm_semiring.of_add_submonoids`.
* `A : ι → subgroup S`:
  `direct_sum.gsemiring.of_add_subgroups`, `direct_sum.gcomm_semiring.of_add_subgroups`.
* `A : ι → submodule S`:
  `direct_sum.gsemiring.of_submodules`, `direct_sum.gcomm_semiring.of_submodules`.

If `complete_lattice.independent (set.range A)`, these provide a gradation of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.

## tags

graded ring, filtered ring, direct sum, add_submonoid
-/


variable {ι : Type _} [DecidableEq ι]

namespace DirectSum

open_locale DirectSum

/-! ### Typeclasses -/


section Defs

variable (A : ι → Type _)

/-- A graded version of `non_unital_non_assoc_semiring`. -/
class gnon_unital_non_assoc_semiring [Add ι] [∀ i, AddCommMonoidₓ (A i)] extends GradedMonoid.GhasMul A where
  mul_zero : ∀ {i j} a : A i, mul a (0 : A j) = 0
  zero_mul : ∀ {i j} b : A j, mul (0 : A i) b = 0
  mul_add : ∀ {i j} a : A i b c : A j, mul a (b + c) = mul a b + mul a c
  add_mul : ∀ {i j} a b : A i c : A j, mul (a + b) c = mul a c + mul b c

end Defs

section Defs

variable (A : ι → Type _)

/-- A graded version of `semiring`. -/
class gsemiring [AddMonoidₓ ι] [∀ i, AddCommMonoidₓ (A i)] extends gnon_unital_non_assoc_semiring A,
  GradedMonoid.Gmonoid A

/-- A graded version of `comm_semiring`. -/
class gcomm_semiring [AddCommMonoidₓ ι] [∀ i, AddCommMonoidₓ (A i)] extends gsemiring A, GradedMonoid.GcommMonoid A

end Defs

theorem of_eq_of_graded_monoid_eq {A : ι → Type _} [∀ i : ι, AddCommMonoidₓ (A i)] {i j : ι} {a : A i} {b : A j}
    (h : GradedMonoid.mk i a = GradedMonoid.mk j b) : DirectSum.of A i a = DirectSum.of A j b :=
  Dfinsupp.single_eq_of_sigma_eq h

variable (A : ι → Type _)

/-! ### Instances for `⨁ i, A i` -/


section One

variable [Zero ι] [GradedMonoid.GhasOne A] [∀ i, AddCommMonoidₓ (A i)]

instance : One (⨁ i, A i) where
  one := DirectSum.of (fun i => A i) 0 GradedMonoid.GhasOne.one

end One

section Mul

variable [Add ι] [∀ i, AddCommMonoidₓ (A i)] [gnon_unital_non_assoc_semiring A]

open add_monoid_hom (flip_apply coe_comp comp_hom_apply_apply)

/-- The piecewise multiplication from the `has_mul` instance, as a bundled homomorphism. -/
@[simps]
def gmul_hom {i j} : A i →+ A j →+ A (i + j) where
  toFun := fun a =>
    { toFun := fun b => GradedMonoid.GhasMul.mul a b, map_zero' := gnon_unital_non_assoc_semiring.mul_zero _,
      map_add' := gnon_unital_non_assoc_semiring.mul_add _ }
  map_zero' := AddMonoidHom.ext fun a => gnon_unital_non_assoc_semiring.zero_mul a
  map_add' := fun a₁ a₂ => AddMonoidHom.ext fun b => gnon_unital_non_assoc_semiring.add_mul _ _ _

/-- The multiplication from the `has_mul` instance, as a bundled homomorphism. -/
def MulHom : (⨁ i, A i) →+ (⨁ i, A i) →+ ⨁ i, A i :=
  DirectSum.toAddMonoid fun i =>
    AddMonoidHom.flip <|
      DirectSum.toAddMonoid fun j => AddMonoidHom.flip <| (DirectSum.of A _).compHom.comp <| gmul_hom A

instance : NonUnitalNonAssocSemiring (⨁ i, A i) :=
  { DirectSum.addCommMonoid _ _ with mul := fun a b => MulHom A a b, zero := 0, add := · + ·,
    zero_mul := fun a => by
      simp only [AddMonoidHom.map_zero, AddMonoidHom.zero_apply],
    mul_zero := fun a => by
      simp only [AddMonoidHom.map_zero],
    left_distrib := fun a b c => by
      simp only [AddMonoidHom.map_add],
    right_distrib := fun a b c => by
      simp only [AddMonoidHom.map_add, AddMonoidHom.add_apply] }

variable {A}

theorem mul_hom_of_of {i j} (a : A i) (b : A j) :
    MulHom A (of _ i a) (of _ j b) = of _ (i + j) (GradedMonoid.GhasMul.mul a b) := by
  unfold MulHom
  rw [to_add_monoid_of, flip_apply, to_add_monoid_of, flip_apply, coe_comp, Function.comp_app, comp_hom_apply_apply,
    coe_comp, Function.comp_app, gmul_hom_apply_apply]

theorem of_mul_of {i j} (a : A i) (b : A j) : of _ i a * of _ j b = of _ (i + j) (GradedMonoid.GhasMul.mul a b) :=
  mul_hom_of_of a b

end Mul

section Semiringₓ

variable [∀ i, AddCommMonoidₓ (A i)] [AddMonoidₓ ι] [gsemiring A]

open add_monoid_hom (flipHom coe_comp comp_hom_apply_apply flip_apply flip_hom_apply)

private theorem one_mulₓ (x : ⨁ i, A i) : 1 * x = x := by
  suffices MulHom A 1 = AddMonoidHom.id (⨁ i, A i) from AddMonoidHom.congr_fun this x
  apply add_hom_ext
  intro i xi
  unfold One.one
  rw [mul_hom_of_of]
  exact of_eq_of_graded_monoid_eq (one_mulₓ <| GradedMonoid.mk i xi)

private theorem mul_oneₓ (x : ⨁ i, A i) : x * 1 = x := by
  suffices (MulHom A).flip 1 = AddMonoidHom.id (⨁ i, A i) from AddMonoidHom.congr_fun this x
  apply add_hom_ext
  intro i xi
  unfold One.one
  rw [flip_apply, mul_hom_of_of]
  exact of_eq_of_graded_monoid_eq (mul_oneₓ <| GradedMonoid.mk i xi)

private theorem mul_assoc (a b c : ⨁ i, A i) : a * b * c = a * (b * c) := by
  suffices
    (MulHom A).compHom.comp (MulHom A) = (AddMonoidHom.compHom flip_hom <| (MulHom A).flip.compHom.comp (MulHom A)).flip
    from AddMonoidHom.congr_fun (AddMonoidHom.congr_fun (AddMonoidHom.congr_fun this a) b) c
  ext ai ax bi bx ci cx : 6
  dsimp only [coe_comp, Function.comp_app, comp_hom_apply_apply, flip_apply, flip_hom_apply]
  rw [mul_hom_of_of, mul_hom_of_of, mul_hom_of_of, mul_hom_of_of]
  exact of_eq_of_graded_monoid_eq (mul_assoc (GradedMonoid.mk ai ax) ⟨bi, bx⟩ ⟨ci, cx⟩)

/-- The `semiring` structure derived from `gsemiring A`. -/
instance Semiringₓ : Semiringₓ (⨁ i, A i) :=
  { DirectSum.nonUnitalNonAssocSemiring _ with one := 1, mul := · * ·, zero := 0, add := · + ·, one_mul := one_mulₓ A,
    mul_one := mul_oneₓ A, mul_assoc := mul_assoc A }

theorem of_pow {i} (a : A i) (n : ℕ) : of _ i a ^ n = of _ (n • i) (GradedMonoid.Gmonoid.gnpow _ a) := by
  induction' n with n
  · exact of_eq_of_graded_monoid_eq (pow_zeroₓ <| GradedMonoid.mk _ a).symm
    
  · rw [pow_succₓ, n_ih, of_mul_of]
    exact of_eq_of_graded_monoid_eq (pow_succₓ (GradedMonoid.mk _ a) n).symm
    

theorem of_list_dprod {α} (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) :
    of A _ (l.dprod fι fA) = (l.map fun a => of A (fι a) (fA a)).Prod := by
  induction l
  · simp only [List.map_nil, List.prod_nil, List.dprod_nil]
    rfl
    
  · simp only [List.map_cons, List.prod_cons, List.dprod_cons, ← l_ih, DirectSum.of_mul_of]
    rfl
    

theorem list_prod_of_fn_of_eq_dprod (n : ℕ) (fι : Finₓ n → ι) (fA : ∀ a, A (fι a)) :
    (List.ofFnₓ fun a => of A (fι a) (fA a)).Prod = of A _ ((List.finRange n).dprod fι fA) := by
  rw [List.of_fn_eq_map, of_list_dprod]

open_locale BigOperators

/-- A heavily unfolded version of the definition of multiplication -/
theorem mul_eq_sum_support_ghas_mul [∀ i : ι x : A i, Decidable (x ≠ 0)] (a a' : ⨁ i, A i) :
    a * a' =
      ∑ ij : ι × ι in (Dfinsupp.support a).product (Dfinsupp.support a'),
        DirectSum.of _ _ (GradedMonoid.GhasMul.mul (a ij.fst) (a' ij.snd)) :=
  by
  change DirectSum.mulHom _ a a' = _
  dsimp [DirectSum.mulHom, DirectSum.toAddMonoid, Dfinsupp.lift_add_hom_apply]
  simp only [Dfinsupp.sum_add_hom_apply, Dfinsupp.sum, Dfinsupp.finset_sum_apply, AddMonoidHom.coe_sum,
    Finset.sum_apply, AddMonoidHom.flip_apply, AddMonoidHom.comp_hom_apply_apply, AddMonoidHom.comp_apply,
    DirectSum.gmul_hom_apply_apply]
  rw [Finset.sum_product]

end Semiringₓ

section CommSemiringₓ

variable [∀ i, AddCommMonoidₓ (A i)] [AddCommMonoidₓ ι] [gcomm_semiring A]

private theorem mul_comm (a b : ⨁ i, A i) : a * b = b * a := by
  suffices MulHom A = (MulHom A).flip from AddMonoidHom.congr_fun (AddMonoidHom.congr_fun this a) b
  apply add_hom_ext
  intro ai ax
  apply add_hom_ext
  intro bi bx
  rw [AddMonoidHom.flip_apply, mul_hom_of_of, mul_hom_of_of]
  exact of_eq_of_graded_monoid_eq (gcomm_semiring.mul_comm ⟨ai, ax⟩ ⟨bi, bx⟩)

/-- The `comm_semiring` structure derived from `gcomm_semiring A`. -/
instance CommSemiringₓ : CommSemiringₓ (⨁ i, A i) :=
  { DirectSum.semiring _ with one := 1, mul := · * ·, zero := 0, add := · + ·, mul_comm := mul_comm A }

end CommSemiringₓ

section Ringₓ

variable [∀ i, AddCommGroupₓ (A i)] [AddCommMonoidₓ ι] [gsemiring A]

/-- The `ring` derived from `gsemiring A`. -/
instance Ringₓ : Ringₓ (⨁ i, A i) :=
  { DirectSum.semiring _, DirectSum.addCommGroup _ with one := 1, mul := · * ·, zero := 0, add := · + ·,
    neg := Neg.neg }

end Ringₓ

section CommRingₓ

variable [∀ i, AddCommGroupₓ (A i)] [AddCommMonoidₓ ι] [gcomm_semiring A]

/-- The `comm_ring` derived from `gcomm_semiring A`. -/
instance CommRingₓ : CommRingₓ (⨁ i, A i) :=
  { DirectSum.ring _, DirectSum.commSemiring _ with one := 1, mul := · * ·, zero := 0, add := · + ·, neg := Neg.neg }

end CommRingₓ

/-! ### Instances for `A 0`

The various `g*` instances are enough to promote the `add_comm_monoid (A 0)` structure to various
types of multiplicative structure.
-/


section GradeZero

section One

variable [Zero ι] [GradedMonoid.GhasOne A] [∀ i, AddCommMonoidₓ (A i)]

@[simp]
theorem of_zero_one : of _ 0 (1 : A 0) = 1 :=
  rfl

end One

section Mul

variable [AddMonoidₓ ι] [∀ i, AddCommMonoidₓ (A i)] [gnon_unital_non_assoc_semiring A]

@[simp]
theorem of_zero_smul {i} (a : A 0) (b : A i) : of _ _ (a • b) = of _ _ a * of _ _ b :=
  (of_eq_of_graded_monoid_eq (GradedMonoid.mk_zero_smul a b)).trans (of_mul_of _ _).symm

@[simp]
theorem of_zero_mul (a b : A 0) : of _ 0 (a * b) = of _ 0 a * of _ 0 b :=
  of_zero_smul A a b

instance grade_zero.non_unital_non_assoc_semiring : NonUnitalNonAssocSemiring (A 0) :=
  Function.Injective.nonUnitalNonAssocSemiring (of A 0) Dfinsupp.single_injective (of A 0).map_zero (of A 0).map_add
    (of_zero_mul A)

instance grade_zero.smul_with_zero (i : ι) : SmulWithZero (A 0) (A i) := by
  let this' := SmulWithZero.compHom (⨁ i, A i) (of A 0).toZeroHom
  refine' dfinsupp.single_injective.smul_with_zero (of A i).toZeroHom (of_zero_smul A)

end Mul

section Semiringₓ

variable [∀ i, AddCommMonoidₓ (A i)] [AddMonoidₓ ι] [gsemiring A]

/-- The `semiring` structure derived from `gsemiring A`. -/
instance grade_zero.semiring : Semiringₓ (A 0) :=
  Function.Injective.semiring (of A 0) Dfinsupp.single_injective (of A 0).map_zero (of_zero_one A) (of A 0).map_add
    (of_zero_mul A)

/-- `of A 0` is a `ring_hom`, using the `direct_sum.grade_zero.semiring` structure. -/
def of_zero_ring_hom : A 0 →+* ⨁ i, A i :=
  { of _ 0 with map_one' := of_zero_one A, map_mul' := of_zero_mul A }

/-- Each grade `A i` derives a `A 0`-module structure from `gsemiring A`. Note that this results
in an overall `module (A 0) (⨁ i, A i)` structure via `direct_sum.module`.
-/
instance grade_zero.module {i} : Module (A 0) (A i) := by
  let this' := Module.compHom (⨁ i, A i) (of_zero_ring_hom A)
  exact dfinsupp.single_injective.module (A 0) (of A i) fun a => of_zero_smul A a

end Semiringₓ

section CommSemiringₓ

variable [∀ i, AddCommMonoidₓ (A i)] [AddCommMonoidₓ ι] [gcomm_semiring A]

/-- The `comm_semiring` structure derived from `gcomm_semiring A`. -/
instance grade_zero.comm_semiring : CommSemiringₓ (A 0) :=
  Function.Injective.commSemiring (of A 0) Dfinsupp.single_injective (of A 0).map_zero (of_zero_one A) (of A 0).map_add
    (of_zero_mul A)

end CommSemiringₓ

section Ringₓ

variable [∀ i, AddCommGroupₓ (A i)] [AddCommMonoidₓ ι] [gsemiring A]

/-- The `ring` derived from `gsemiring A`. -/
instance grade_zero.ring : Ringₓ (A 0) :=
  Function.Injective.ring (of A 0) Dfinsupp.single_injective (of A 0).map_zero (of_zero_one A) (of A 0).map_add
    (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub

end Ringₓ

section CommRingₓ

variable [∀ i, AddCommGroupₓ (A i)] [AddCommMonoidₓ ι] [gcomm_semiring A]

/-- The `comm_ring` derived from `gcomm_semiring A`. -/
instance grade_zero.comm_ring : CommRingₓ (A 0) :=
  Function.Injective.commRing (of A 0) Dfinsupp.single_injective (of A 0).map_zero (of_zero_one A) (of A 0).map_add
    (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub

end CommRingₓ

end GradeZero

section ToSemiring

variable {R : Type _} [∀ i, AddCommMonoidₓ (A i)] [AddMonoidₓ ι] [gsemiring A] [Semiringₓ R]

variable {A}

/-- If two ring homomorphisms from `⨁ i, A i` are equal on each `of A i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem ring_hom_ext' ⦃F G : (⨁ i, A i) →+* R⦄ (h : ∀ i, (↑F : _ →+ R).comp (of A i) = (↑G : _ →+ R).comp (of A i)) :
    F = G :=
  RingHom.coe_add_monoid_hom_injective <| DirectSum.add_hom_ext' h

/-- Two `ring_hom`s out of a direct sum are equal if they agree on the generators. -/
theorem ring_hom_ext ⦃f g : (⨁ i, A i) →+* R⦄ (h : ∀ i x, f (of A i x) = g (of A i x)) : f = g :=
  ring_hom_ext' fun i => AddMonoidHom.ext <| h i

/-- A family of `add_monoid_hom`s preserving `direct_sum.ghas_one.one` and `direct_sum.ghas_mul.mul`
describes a `ring_hom`s on `⨁ i, A i`. This is a stronger version of `direct_sum.to_monoid`.

Of particular interest is the case when `A i` are bundled subojects, `f` is the family of
coercions such as `add_submonoid.subtype (A i)`, and the `[gsemiring A]` structure originates from
`direct_sum.gsemiring.of_add_submonoids`, in which case the proofs about `ghas_one` and `ghas_mul`
can be discharged by `rfl`. -/
@[simps]
def to_semiring (f : ∀ i, A i →+ R) (hone : f _ GradedMonoid.GhasOne.one = 1)
    (hmul : ∀ {i j} ai : A i aj : A j, f _ (GradedMonoid.GhasMul.mul ai aj) = f _ ai * f _ aj) : (⨁ i, A i) →+* R :=
  { to_add_monoid f with toFun := to_add_monoid f,
    map_one' := by
      change (to_add_monoid f) (of _ 0 _) = 1
      rw [to_add_monoid_of]
      exact hone,
    map_mul' := by
      rw [(to_add_monoid f).map_mul_iff]
      ext xi xv yi yv : 4
      show to_add_monoid f (of A xi xv * of A yi yv) = to_add_monoid f (of A xi xv) * to_add_monoid f (of A yi yv)
      rw [of_mul_of, to_add_monoid_of, to_add_monoid_of, to_add_monoid_of]
      exact hmul _ _ }

@[simp]
theorem to_semiring_of (f : ∀ i, A i →+ R) hone hmul (i : ι) (x : A i) : to_semiring f hone hmul (of _ i x) = f _ x :=
  to_add_monoid_of f i x

@[simp]
theorem to_semiring_coe_add_monoid_hom (f : ∀ i, A i →+ R) hone hmul :
    (to_semiring f hone hmul : (⨁ i, A i) →+ R) = to_add_monoid f :=
  rfl

/-- Families of `add_monoid_hom`s preserving `direct_sum.ghas_one.one` and `direct_sum.ghas_mul.mul`
are isomorphic to `ring_hom`s on `⨁ i, A i`. This is a stronger version of `dfinsupp.lift_add_hom`.
-/
@[simps]
def lift_ring_hom :
    { f : ∀ {i}, A i →+ R //
        f GradedMonoid.GhasOne.one = 1 ∧ ∀ {i j} ai : A i aj : A j, f (GradedMonoid.GhasMul.mul ai aj) = f ai * f aj } ≃
      ((⨁ i, A i) →+* R) where
  toFun := fun f => to_semiring f.1 f.2.1 f.2.2
  invFun := fun F =>
    ⟨fun i => (F : (⨁ i, A i) →+ R).comp (of _ i), by
      simp only [AddMonoidHom.comp_apply, RingHom.coe_add_monoid_hom]
      rw [← F.map_one]
      rfl, fun i j ai aj => by
      simp only [AddMonoidHom.comp_apply, RingHom.coe_add_monoid_hom]
      rw [← F.map_mul, of_mul_of]⟩
  left_inv := fun f => by
    ext xi xv
    exact to_add_monoid_of f.1 xi xv
  right_inv := fun F => by
    apply RingHom.coe_add_monoid_hom_injective
    ext xi xv
    simp only [RingHom.coe_add_monoid_hom_mk, DirectSum.to_add_monoid_of, AddMonoidHom.mk_coe, AddMonoidHom.comp_apply,
      to_semiring_coe_add_monoid_hom]

end ToSemiring

end DirectSum

/-! ### Concrete instances -/


section Uniform

variable (ι)

/-- A direct sum of copies of a `semiring` inherits the multiplication structure. -/
instance NonUnitalNonAssocSemiring.directSumGnonUnitalNonAssocSemiring {R : Type _} [AddMonoidₓ ι]
    [NonUnitalNonAssocSemiring R] : DirectSum.GnonUnitalNonAssocSemiring fun i : ι => R :=
  { Mul.ghasMul ι with mul_zero := fun i j => mul_zero, zero_mul := fun i j => zero_mul, mul_add := fun i j => mul_addₓ,
    add_mul := fun i j => add_mulₓ }

/-- A direct sum of copies of a `semiring` inherits the multiplication structure. -/
instance Semiringₓ.directSumGsemiring {R : Type _} [AddMonoidₓ ι] [Semiringₓ R] : DirectSum.Gsemiring fun i : ι => R :=
  { NonUnitalNonAssocSemiring.directSumGnonUnitalNonAssocSemiring ι, Monoidₓ.gmonoid ι with }

open_locale DirectSum

example {R : Type _} [AddMonoidₓ ι] [Semiringₓ R] (i j : ι) (a b : R) :
    (DirectSum.of _ i a * DirectSum.of _ j b : ⨁ i, R) = DirectSum.of _ (i + j) (a * b) := by
  rw [DirectSum.of_mul_of, Mul.ghas_mul_mul]

/-- A direct sum of copies of a `comm_semiring` inherits the commutative multiplication structure.
-/
instance CommSemiringₓ.directSumGcommSemiring {R : Type _} [AddCommMonoidₓ ι] [CommSemiringₓ R] :
    DirectSum.GcommSemiring fun i : ι => R :=
  { CommMonoidₓ.gcommMonoid ι, Semiringₓ.directSumGsemiring ι with }

end Uniform

