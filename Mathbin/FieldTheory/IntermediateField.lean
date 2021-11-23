import Mathbin.FieldTheory.Subfield 
import Mathbin.FieldTheory.Tower 
import Mathbin.RingTheory.Algebraic

/-!
# Intermediate fields

Let `L / K` be a field extension, given as an instance `algebra K L`.
This file defines the type of fields in between `K` and `L`, `intermediate_field K L`.
An `intermediate_field K L` is a subfield of `L` which contains (the image of) `K`,
i.e. it is a `subfield L` and a `subalgebra K L`.

## Main definitions

 * `intermediate_field K L` : the type of intermediate fields between `K` and `L`.

 * `subalgebra.to_intermediate_field`: turns a subalgebra closed under `⁻¹`
   into an intermediate field

 * `subfield.to_intermediate_field`: turns a subfield containing the image of `K`
   into an intermediate field

* `intermediate_field.map`: map an intermediate field along an `alg_hom`

## Implementation notes

Intermediate fields are defined with a structure extending `subfield` and `subalgebra`.
A `subalgebra` is closed under all operations except `⁻¹`,

## Tags
intermediate field, field extension
-/


open FiniteDimensional

open_locale BigOperators

variable(K L : Type _)[Field K][Field L][Algebra K L]

/-- `S : intermediate_field K L` is a subset of `L` such that there is a field
tower `L / S / K`. -/
structure IntermediateField extends Subalgebra K L where 
  neg_mem' : ∀ x _ : x ∈ carrier, -x ∈ carrier 
  inv_mem' : ∀ x _ : x ∈ carrier, x⁻¹ ∈ carrier

/-- Reinterpret an `intermediate_field` as a `subalgebra`. -/
add_decl_doc IntermediateField.toSubalgebra

variable{K L}(S : IntermediateField K L)

namespace IntermediateField

/-- Reinterpret an `intermediate_field` as a `subfield`. -/
def to_subfield : Subfield L :=
  { S.to_subalgebra, S with  }

instance  : SetLike (IntermediateField K L) L :=
  ⟨fun S => S.to_subalgebra.carrier,
    by 
      rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨h⟩
      congr⟩

@[simp]
theorem mem_carrier {s : IntermediateField K L} {x : L} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

/-- Two intermediate fields are equal if they have the same elements. -/
@[ext]
theorem ext {S T : IntermediateField K L} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem coe_to_subalgebra : (S.to_subalgebra : Set L) = S :=
  rfl

@[simp]
theorem coe_to_subfield : (S.to_subfield : Set L) = S :=
  rfl

@[simp]
theorem mem_mk (s : Set L) (hK : ∀ x, algebraMap K L x ∈ s) ho hm hz ha hn hi (x : L) :
  x ∈ IntermediateField.mk (Subalgebra.mk s ho hm hz ha hK) hn hi ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mem_to_subalgebra (s : IntermediateField K L) (x : L) : x ∈ s.to_subalgebra ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mem_to_subfield (s : IntermediateField K L) (x : L) : x ∈ s.to_subfield ↔ x ∈ s :=
  Iff.rfl

/-- An intermediate field contains the image of the smaller field. -/
theorem algebra_map_mem (x : K) : algebraMap K L x ∈ S :=
  S.algebra_map_mem' x

/-- An intermediate field contains the ring's 1. -/
theorem one_mem : (1 : L) ∈ S :=
  S.one_mem'

/-- An intermediate field contains the ring's 0. -/
theorem zero_mem : (0 : L) ∈ S :=
  S.zero_mem'

/-- An intermediate field is closed under multiplication. -/
theorem mul_mem : ∀ {x y : L}, x ∈ S → y ∈ S → (x*y) ∈ S :=
  S.mul_mem'

/-- An intermediate field is closed under scalar multiplication. -/
theorem smul_mem {y : L} : y ∈ S → ∀ {x : K}, x • y ∈ S :=
  S.to_subalgebra.smul_mem

/-- An intermediate field is closed under addition. -/
theorem add_mem : ∀ {x y : L}, x ∈ S → y ∈ S → (x+y) ∈ S :=
  S.add_mem'

/-- An intermediate field is closed under subtraction -/
theorem sub_mem {x y : L} (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
  S.to_subfield.sub_mem hx hy

/-- An intermediate field is closed under negation. -/
theorem neg_mem : ∀ {x : L}, x ∈ S → -x ∈ S :=
  S.neg_mem'

/-- An intermediate field is closed under inverses. -/
theorem inv_mem : ∀ {x : L}, x ∈ S → x⁻¹ ∈ S :=
  S.inv_mem'

/-- An intermediate field is closed under division. -/
theorem div_mem {x y : L} (hx : x ∈ S) (hy : y ∈ S) : x / y ∈ S :=
  S.to_subfield.div_mem hx hy

/-- Product of a list of elements in an intermediate_field is in the intermediate_field. -/
theorem list_prod_mem {l : List L} : (∀ x _ : x ∈ l, x ∈ S) → l.prod ∈ S :=
  S.to_subfield.list_prod_mem

/-- Sum of a list of elements in an intermediate field is in the intermediate_field. -/
theorem list_sum_mem {l : List L} : (∀ x _ : x ∈ l, x ∈ S) → l.sum ∈ S :=
  S.to_subfield.list_sum_mem

/-- Product of a multiset of elements in an intermediate field is in the intermediate_field. -/
theorem multiset_prod_mem (m : Multiset L) : (∀ a _ : a ∈ m, a ∈ S) → m.prod ∈ S :=
  S.to_subfield.multiset_prod_mem m

/-- Sum of a multiset of elements in a `intermediate_field` is in the `intermediate_field`. -/
theorem multiset_sum_mem (m : Multiset L) : (∀ a _ : a ∈ m, a ∈ S) → m.sum ∈ S :=
  S.to_subfield.multiset_sum_mem m

/-- Product of elements of an intermediate field indexed by a `finset` is in the intermediate_field.
-/
theorem prod_mem {ι : Type _} {t : Finset ι} {f : ι → L} (h : ∀ c _ : c ∈ t, f c ∈ S) : (∏i in t, f i) ∈ S :=
  S.to_subfield.prod_mem h

/-- Sum of elements in a `intermediate_field` indexed by a `finset` is in the `intermediate_field`.
-/
theorem sum_mem {ι : Type _} {t : Finset ι} {f : ι → L} (h : ∀ c _ : c ∈ t, f c ∈ S) : (∑i in t, f i) ∈ S :=
  S.to_subfield.sum_mem h

theorem pow_mem {x : L} (hx : x ∈ S) : ∀ n : ℤ, (x^n) ∈ S
| (n : ℕ) =>
  by 
    rw [zpow_coe_nat]
    exact S.to_subfield.pow_mem hx _
| -[1+ n] =>
  by 
    rw [zpow_neg_succ_of_nat]
    exact S.to_subfield.inv_mem (S.to_subfield.pow_mem hx _)

theorem zsmul_mem {x : L} (hx : x ∈ S) (n : ℤ) : n • x ∈ S :=
  S.to_subfield.zsmul_mem hx n

theorem coe_int_mem (n : ℤ) : (n : L) ∈ S :=
  by 
    simp only [←zsmul_one, zsmul_mem, one_mem]

end IntermediateField

/-- Turn a subalgebra closed under inverses into an intermediate field -/
def Subalgebra.toIntermediateField (S : Subalgebra K L) (inv_mem : ∀ x _ : x ∈ S, x⁻¹ ∈ S) : IntermediateField K L :=
  { S with neg_mem' := fun x => S.neg_mem, inv_mem' := inv_mem }

@[simp]
theorem to_subalgebra_to_intermediate_field (S : Subalgebra K L) (inv_mem : ∀ x _ : x ∈ S, x⁻¹ ∈ S) :
  (S.to_intermediate_field inv_mem).toSubalgebra = S :=
  by 
    ext 
    rfl

@[simp]
theorem to_intermediate_field_to_subalgebra (S : IntermediateField K L)
  (inv_mem : ∀ x _ : x ∈ S.to_subalgebra, x⁻¹ ∈ S) : S.to_subalgebra.to_intermediate_field inv_mem = S :=
  by 
    ext 
    rfl

/-- Turn a subfield of `L` containing the image of `K` into an intermediate field -/
def Subfield.toIntermediateField (S : Subfield L) (algebra_map_mem : ∀ x, algebraMap K L x ∈ S) :
  IntermediateField K L :=
  { S with algebra_map_mem' := algebra_map_mem }

namespace IntermediateField

/-- An intermediate field inherits a field structure -/
instance to_field : Field S :=
  S.to_subfield.to_field

@[simp, normCast]
theorem coe_add (x y : S) : («expr↑ » (x+y) : L) = «expr↑ » x+«expr↑ » y :=
  rfl

@[simp, normCast]
theorem coe_neg (x : S) : («expr↑ » (-x) : L) = -«expr↑ » x :=
  rfl

@[simp, normCast]
theorem coe_mul (x y : S) : («expr↑ » (x*y) : L) = «expr↑ » x*«expr↑ » y :=
  rfl

@[simp, normCast]
theorem coe_inv (x : S) : («expr↑ » (x⁻¹) : L) = «expr↑ » x⁻¹ :=
  rfl

@[simp, normCast]
theorem coe_zero : ((0 : S) : L) = 0 :=
  rfl

@[simp, normCast]
theorem coe_one : ((1 : S) : L) = 1 :=
  rfl

@[simp, normCast]
theorem coe_pow (x : S) (n : ℕ) : («expr↑ » (x^n) : L) = («expr↑ » x^n) :=
  by 
    induction' n with n ih
    ·
      simp 
    ·
      simp [pow_succₓ, ih]

/-! `intermediate_field`s inherit structure from their `subalgebra` coercions. -/


instance module' {R} [Semiringₓ R] [HasScalar R K] [Module R L] [IsScalarTower R K L] : Module R S :=
  S.to_subalgebra.module'

instance Module : Module K S :=
  S.to_subalgebra.module

instance IsScalarTower {R} [Semiringₓ R] [HasScalar R K] [Module R L] [IsScalarTower R K L] : IsScalarTower R K S :=
  S.to_subalgebra.is_scalar_tower

@[simp]
theorem coe_smul {R} [Semiringₓ R] [HasScalar R K] [Module R L] [IsScalarTower R K L] (r : R) (x : S) :
  «expr↑ » (r • x) = (r • x : L) :=
  rfl

instance algebra' {K'} [CommSemiringₓ K'] [HasScalar K' K] [Algebra K' L] [IsScalarTower K' K L] : Algebra K' S :=
  S.to_subalgebra.algebra'

instance Algebra : Algebra K S :=
  S.to_subalgebra.algebra

instance to_algebra {R : Type _} [Semiringₓ R] [Algebra L R] : Algebra S R :=
  S.to_subalgebra.to_algebra

instance is_scalar_tower_bot {R : Type _} [Semiringₓ R] [Algebra L R] : IsScalarTower S L R :=
  IsScalarTower.subalgebra _ _ _ S.to_subalgebra

instance is_scalar_tower_mid {R : Type _} [Semiringₓ R] [Algebra L R] [Algebra K R] [IsScalarTower K L R] :
  IsScalarTower K S R :=
  IsScalarTower.subalgebra' _ _ _ S.to_subalgebra

/-- Specialize `is_scalar_tower_mid` to the common case where the top field is `L` -/
instance is_scalar_tower_mid' : IsScalarTower K S L :=
  S.is_scalar_tower_mid

variable{L' : Type _}[Field L'][Algebra K L']

/-- If `f : L →+* L'` fixes `K`, `S.map f` is the intermediate field between `L'` and `K`
such that `x ∈ S ↔ f x ∈ S.map f`. -/
def map (f : L →ₐ[K] L') : IntermediateField K L' :=
  { S.to_subalgebra.map f with
    inv_mem' :=
      by 
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x⁻¹, S.inv_mem hx, f.map_inv x⟩,
    neg_mem' := fun x hx => (S.to_subalgebra.map f).neg_mem hx }

/-- The embedding from an intermediate field of `L / K` to `L`. -/
def val : S →ₐ[K] L :=
  S.to_subalgebra.val

@[simp]
theorem coe_val : «expr⇑ » S.val = coeₓ :=
  rfl

@[simp]
theorem val_mk {x : L} (hx : x ∈ S) : S.val ⟨x, hx⟩ = x :=
  rfl

variable{S}

theorem to_subalgebra_injective {S S' : IntermediateField K L} (h : S.to_subalgebra = S'.to_subalgebra) : S = S' :=
  by 
    ext 
    rw [←mem_to_subalgebra, ←mem_to_subalgebra, h]

variable(S)

theorem set_range_subset : Set.Range (algebraMap K L) ⊆ S :=
  S.to_subalgebra.range_subset

theorem field_range_le : (algebraMap K L).fieldRange ≤ S.to_subfield :=
  fun x hx =>
    S.to_subalgebra.range_subset
      (by 
        rwa [Set.mem_range, ←RingHom.mem_field_range])

@[simp]
theorem to_subalgebra_le_to_subalgebra {S S' : IntermediateField K L} : S.to_subalgebra ≤ S'.to_subalgebra ↔ S ≤ S' :=
  Iff.rfl

@[simp]
theorem to_subalgebra_lt_to_subalgebra {S S' : IntermediateField K L} : S.to_subalgebra < S'.to_subalgebra ↔ S < S' :=
  Iff.rfl

variable{S}

section Tower

/-- Lift an intermediate_field of an intermediate_field -/
def lift1 {F : IntermediateField K L} (E : IntermediateField K F) : IntermediateField K L :=
  map E (val F)

/-- Lift an intermediate_field of an intermediate_field -/
def lift2 {F : IntermediateField K L} (E : IntermediateField F L) : IntermediateField K L :=
  { Carrier := E.carrier, zero_mem' := zero_mem E, add_mem' := fun x y => add_mem E, neg_mem' := fun x => neg_mem E,
    one_mem' := one_mem E, mul_mem' := fun x y => mul_mem E, inv_mem' := fun x => inv_mem E,
    algebra_map_mem' := fun x => algebra_map_mem E (algebraMap K F x) }

instance has_lift1 {F : IntermediateField K L} : HasLiftT (IntermediateField K F) (IntermediateField K L) :=
  ⟨lift1⟩

instance has_lift2 {F : IntermediateField K L} : HasLiftT (IntermediateField F L) (IntermediateField K L) :=
  ⟨lift2⟩

@[simp]
theorem mem_lift2 {F : IntermediateField K L} {E : IntermediateField F L} {x : L} :
  x ∈ («expr↑ » E : IntermediateField K L) ↔ x ∈ E :=
  Iff.rfl

/-- This was formerly an instance called `lift2_alg`, but an instance above already provides it. -/
example  {F : IntermediateField K L} {E : IntermediateField F L} : Algebra K E :=
  by 
    infer_instance

theorem lift2_algebra_map {F : IntermediateField K L} {E : IntermediateField F L} :
  algebraMap K E = (algebraMap F E).comp (algebraMap K F) :=
  rfl

instance lift2_tower {F : IntermediateField K L} {E : IntermediateField F L} : IsScalarTower K F E :=
  E.is_scalar_tower

/-- `lift2` is isomorphic to the original `intermediate_field`. -/
def lift2_alg_equiv {F : IntermediateField K L} (E : IntermediateField F L) :
  («expr↑ » E : IntermediateField K L) ≃ₐ[K] E :=
  AlgEquiv.refl

end Tower

section FiniteDimensional

variable(F E : IntermediateField K L)

instance finite_dimensional_left [FiniteDimensional K L] : FiniteDimensional K F :=
  FiniteDimensional.finite_dimensional_submodule F.to_subalgebra.to_submodule

instance finite_dimensional_right [FiniteDimensional K L] : FiniteDimensional F L :=
  right K F L

@[simp]
theorem dim_eq_dim_subalgebra : Module.rank K F.to_subalgebra = Module.rank K F :=
  rfl

@[simp]
theorem finrank_eq_finrank_subalgebra : finrank K F.to_subalgebra = finrank K F :=
  rfl

variable{F}{E}

@[simp]
theorem to_subalgebra_eq_iff : F.to_subalgebra = E.to_subalgebra ↔ F = E :=
  by 
    rw [SetLike.ext_iff, SetLike.ext'_iff, Set.ext_iff]
    rfl

theorem eq_of_le_of_finrank_le [FiniteDimensional K L] (h_le : F ≤ E) (h_finrank : finrank K E ≤ finrank K F) : F = E :=
  to_subalgebra_injective$ Subalgebra.to_submodule_injective$ eq_of_le_of_finrank_le h_le h_finrank

theorem eq_of_le_of_finrank_eq [FiniteDimensional K L] (h_le : F ≤ E) (h_finrank : finrank K F = finrank K E) : F = E :=
  eq_of_le_of_finrank_le h_le h_finrank.ge

-- error in FieldTheory.IntermediateField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_of_le_of_finrank_le'
[finite_dimensional K L]
(h_le : «expr ≤ »(F, E))
(h_finrank : «expr ≤ »(finrank F L, finrank E L)) : «expr = »(F, E) :=
begin
  apply [expr eq_of_le_of_finrank_le h_le],
  have [ident h1] [] [":=", expr finrank_mul_finrank K F L],
  have [ident h2] [] [":=", expr finrank_mul_finrank K E L],
  have [ident h3] [":", expr «expr < »(0, finrank E L)] [":=", expr finrank_pos],
  nlinarith [] [] []
end

theorem eq_of_le_of_finrank_eq' [FiniteDimensional K L] (h_le : F ≤ E) (h_finrank : finrank F L = finrank E L) :
  F = E :=
  eq_of_le_of_finrank_le' h_le h_finrank.le

end FiniteDimensional

end IntermediateField

/-- If `L/K` is algebraic, the `K`-subalgebras of `L` are all fields.  -/
def subalgebraEquivIntermediateField (alg : Algebra.IsAlgebraic K L) : Subalgebra K L ≃o IntermediateField K L :=
  { toFun := fun S => S.to_intermediate_field fun x hx => S.inv_mem_of_algebraic (alg (⟨x, hx⟩ : S)),
    invFun := fun S => S.to_subalgebra, left_inv := fun S => to_subalgebra_to_intermediate_field _ _,
    right_inv := fun S => to_intermediate_field_to_subalgebra _ _, map_rel_iff' := fun S S' => Iff.rfl }

@[simp]
theorem mem_subalgebra_equiv_intermediate_field (alg : Algebra.IsAlgebraic K L) {S : Subalgebra K L} {x : L} :
  x ∈ subalgebraEquivIntermediateField alg S ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem mem_subalgebra_equiv_intermediate_field_symm (alg : Algebra.IsAlgebraic K L) {S : IntermediateField K L}
  {x : L} : x ∈ (subalgebraEquivIntermediateField alg).symm S ↔ x ∈ S :=
  Iff.rfl

