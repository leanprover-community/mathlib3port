import Mathbin.LinearAlgebra.Determinant

/-!
# Orientations of modules and rays in modules

This file defines rays in modules and orientations of modules.

## Main definitions

* `module.ray` is a type for the equivalence class of nonzero vectors in a module with some
common positive multiple.

* `orientation` is a type synonym for `module.ray` for the case where the module is that of
alternating maps from a module to its underlying ring.  An orientation may be associated with an
alternating map or with a basis.

* `module.oriented` is a type class for a choice of orientation of a module that is considered
the positive orientation.

## Implementation notes

`orientation` is defined for an arbitrary index type, but the main intended use case is when
that index type is a `fintype` and there exists a basis of the same cardinality.

## References

* https://en.wikipedia.org/wiki/Orientation_(vector_space)

-/


noncomputable section

open_locale BigOperators

section OrderedCommSemiring

variable (R : Type _) [OrderedCommSemiring R]

variable {M : Type _} [AddCommMonoidₓ M] [Module R M]

variable {N : Type _} [AddCommMonoidₓ N] [Module R N]

variable (ι : Type _) [DecidableEq ι]

/-- Two vectors are in the same ray if some positive multiples of them are equal (in the typical
case over a field, this means each is a positive multiple of the other).  Over a field, this
is equivalent to `mul_action.orbit_rel`. -/
def SameRay (v₁ v₂ : M) : Prop :=
  ∃ r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • v₁ = r₂ • v₂

variable {R}

/-- `same_ray` is reflexive. -/
@[refl]
theorem SameRay.refl [Nontrivial R] (x : M) : SameRay R x x :=
  ⟨1, 1, zero_lt_one, zero_lt_one, rfl⟩

/-- `same_ray` is symmetric. -/
@[symm]
theorem SameRay.symm {x y : M} : SameRay R x y → SameRay R y x := fun ⟨r₁, r₂, hr₁, hr₂, h⟩ =>
  ⟨r₂, r₁, hr₂, hr₁, h.symm⟩

/-- `same_ray` is transitive. -/
@[trans]
theorem SameRay.trans {x y z : M} : SameRay R x y → SameRay R y z → SameRay R x z :=
  fun ⟨r₁, r₂, hr₁, hr₂, h₁⟩ ⟨r₃, r₄, hr₃, hr₄, h₂⟩ =>
  ⟨r₃ * r₁, r₂ * r₄, mul_pos hr₃ hr₁, mul_pos hr₂ hr₄, by
    rw [mul_smul, mul_smul, h₁, ← h₂, smul_comm]⟩

theorem same_ray_comm {x y : M} : SameRay R x y ↔ SameRay R y x :=
  ⟨SameRay.symm, SameRay.symm⟩

variable (R M)

/-- `same_ray` is an equivalence relation. -/
theorem equivalence_same_ray [Nontrivial R] : Equivalenceₓ (SameRay R : M → M → Prop) :=
  ⟨SameRay.refl, fun _ _ => SameRay.symm, fun _ _ _ => SameRay.trans⟩

variable {R M}

/-- A vector is in the same ray as a positive multiple of itself. -/
theorem same_ray_pos_smul_right (v : M) {r : R} (h : 0 < r) : SameRay R v (r • v) :=
  ⟨r, 1, h,
    let f := nontrivial_of_lt _ _ h
    zero_lt_one,
    (one_smul _ _).symm⟩

/-- A vector is in the same ray as a positive multiple of one it is in the same ray as. -/
theorem SameRay.pos_smul_right {v₁ v₂ : M} {r : R} (h : SameRay R v₁ v₂) (hr : 0 < r) : SameRay R v₁ (r • v₂) :=
  h.trans (same_ray_pos_smul_right v₂ hr)

/-- A positive multiple of a vector is in the same ray as that vector. -/
theorem same_ray_pos_smul_left (v : M) {r : R} (h : 0 < r) : SameRay R (r • v) v :=
  ⟨1, r,
    let f := nontrivial_of_lt _ _ h
    zero_lt_one,
    h, one_smul _ _⟩

/-- A positive multiple of a vector is in the same ray as one it is in the same ray as. -/
theorem SameRay.pos_smul_left {v₁ v₂ : M} {r : R} (h : SameRay R v₁ v₂) (hr : 0 < r) : SameRay R (r • v₁) v₂ :=
  (same_ray_pos_smul_left v₁ hr).trans h

/-- If two vectors are on the same ray then they remain so after appling a linear map. -/
theorem SameRay.map {v₁ v₂ : M} (f : M →ₗ[R] N) (h : SameRay R v₁ v₂) : SameRay R (f v₁) (f v₂) :=
  let ⟨r₁, r₂, hr₁, hr₂, h⟩ := h
  ⟨r₁, r₂, hr₁, hr₂, by
    rw [← f.map_smul, ← f.map_smul, h]⟩

/-- If two vectors are on the same ray then they remain so after appling a linear equivalence. -/
@[simp]
theorem same_ray_map_iff {v₁ v₂ : M} (e : M ≃ₗ[R] N) : SameRay R (e v₁) (e v₂) ↔ SameRay R v₁ v₂ :=
  ⟨fun h => by
    simpa using SameRay.map e.symm.to_linear_map h, SameRay.map e.to_linear_map⟩

/-- If two vectors are on the same ray then both scaled by the same action are also on the same
ray. -/
theorem SameRay.smul {S : Type _} [HasScalar S M] [SmulCommClass R S M] {v₁ v₂ : M} (s : S) (h : SameRay R v₁ v₂) :
    SameRay R (s • v₁) (s • v₂) :=
  let ⟨r₁, r₂, hr₁, hr₂, h⟩ := h
  ⟨r₁, r₂, hr₁, hr₂, by
    rw [smul_comm r₁ s v₁, smul_comm r₂ s v₂, h]⟩

variable (R M)

/-- The setoid of the `same_ray` relation for elements of a module. -/
def sameRaySetoid [Nontrivial R] : Setoidₓ M where
  R := SameRay R
  iseqv := equivalence_same_ray R M

/-- Nonzero vectors, as used to define rays. -/
@[reducible]
def RayVector :=
  { v : M // v ≠ 0 }

/-- The setoid of the `same_ray` relation for the subtype of nonzero vectors. -/
def RayVector.sameRaySetoid [Nontrivial R] : Setoidₓ (RayVector M) :=
  (sameRaySetoid R M).comap coe

attribute [local instance] RayVector.sameRaySetoid

variable {R M}

/-- Equivalence of nonzero vectors, in terms of same_ray. -/
theorem equiv_iff_same_ray [Nontrivial R] (v₁ v₂ : RayVector M) : v₁ ≈ v₂ ↔ SameRay R (v₁ : M) v₂ :=
  Iff.rfl

variable (R M)

/-- A ray (equivalence class of nonzero vectors with common positive multiples) in a module. -/
@[nolint has_inhabited_instance]
def Module.Ray [Nontrivial R] :=
  Quotientₓ (RayVector.sameRaySetoid R M)

/-- An orientation of a module, intended to be used when `ι` is a `fintype` with the same
cardinality as a basis. -/
abbrev Orientation [Nontrivial R] :=
  Module.Ray R (AlternatingMap R M R ι)

/-- A type class fixing an orientation of a module. -/
class Module.Oriented [Nontrivial R] where
  positiveOrientation : Orientation R M ι

variable {M}

/-- The ray given by a nonzero vector. -/
protected def rayOfNeZero [Nontrivial R] (v : M) (h : v ≠ 0) : Module.Ray R M :=
  ⟦⟨v, h⟩⟧

/-- An induction principle for `module.ray`, used as `induction x using module.ray.ind`. -/
theorem Module.Ray.ind [Nontrivial R] {C : Module.Ray R M → Prop} (h : ∀ v hv : v ≠ 0, C (rayOfNeZero R v hv))
    (x : Module.Ray R M) : C x :=
  Quotientₓ.ind (Subtype.rec <| h) x

/-- The rays given by two nonzero vectors are equal if and only if those vectors
satisfy `same_ray`. -/
theorem ray_eq_iff [Nontrivial R] {v₁ v₂ : M} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    rayOfNeZero R _ hv₁ = rayOfNeZero R _ hv₂ ↔ SameRay R v₁ v₂ :=
  Quotientₓ.eq

variable {R}

/-- The ray given by a positive multiple of a nonzero vector. -/
@[simp]
theorem ray_pos_smul [Nontrivial R] {v : M} (h : v ≠ 0) {r : R} (hr : 0 < r) (hrv : r • v ≠ 0) :
    rayOfNeZero R _ hrv = rayOfNeZero R _ h := by
  rw [ray_eq_iff]
  exact same_ray_pos_smul_left v hr

/-- An equivalence between modules implies an equivalence between ray vectors. -/
def RayVector.mapLinearEquiv (e : M ≃ₗ[R] N) : RayVector M ≃ RayVector N :=
  (Equivₓ.subtypeEquiv e.to_equiv) fun _ => e.map_ne_zero_iff.symm

/-- An equivalence between modules implies an equivalence between rays. -/
def Module.Ray.map [Nontrivial R] (e : M ≃ₗ[R] N) : Module.Ray R M ≃ Module.Ray R N :=
  (Quotientₓ.congr (RayVector.mapLinearEquiv e)) fun ⟨a, ha⟩ ⟨b, hb⟩ => (same_ray_map_iff _).symm

@[simp]
theorem Module.Ray.map_apply [Nontrivial R] (e : M ≃ₗ[R] N) (v : M) (hv : v ≠ 0) :
    Module.Ray.map e (rayOfNeZero _ v hv) = rayOfNeZero _ (e v) (e.map_ne_zero_iff.2 hv) :=
  rfl

@[simp]
theorem Module.Ray.map_refl [Nontrivial R] : (Module.Ray.map <| LinearEquiv.refl R M) = Equivₓ.refl _ :=
  Equivₓ.ext <| (Module.Ray.ind R) fun _ _ => rfl

@[simp]
theorem Module.Ray.map_symm [Nontrivial R] (e : M ≃ₗ[R] N) : (Module.Ray.map e).symm = Module.Ray.map e.symm :=
  rfl

/-- An equivalence between modules implies an equivalence between orientations. -/
def Orientation.map [Nontrivial R] (e : M ≃ₗ[R] N) : Orientation R M ι ≃ Orientation R N ι :=
  Module.Ray.map <| AlternatingMap.domLcongr R R ι R e

@[simp]
theorem Orientation.map_apply [Nontrivial R] (e : M ≃ₗ[R] N) (v : AlternatingMap R M R ι) (hv : v ≠ 0) :
    Orientation.map ι e (rayOfNeZero _ v hv) =
      rayOfNeZero _ (v.comp_linear_map e.symm) (mt (v.comp_linear_equiv_eq_zero_iff e.symm).mp hv) :=
  rfl

@[simp]
theorem Orientation.map_refl [Nontrivial R] : (Orientation.map ι <| LinearEquiv.refl R M) = Equivₓ.refl _ := by
  rw [Orientation.map, AlternatingMap.dom_lcongr_refl, Module.Ray.map_refl]

@[simp]
theorem Orientation.map_symm [Nontrivial R] (e : M ≃ₗ[R] N) : (Orientation.map ι e).symm = Orientation.map ι e.symm :=
  rfl

section Action

variable {G : Type _} [Groupₓ G] [Nontrivial R] [DistribMulAction G M] [SmulCommClass R G M]

/-- Any invertible action preserves the non-zeroness of ray vectors. This is primarily of interest
when `G = Rˣ` -/
instance : MulAction G (RayVector M) where
  smul := fun r => (Subtype.map ((· • ·) r)) fun a => (smul_ne_zero_iff_ne _).2
  mul_smul := fun a b m => Subtype.ext <| mul_smul a b _
  one_smul := fun m => Subtype.ext <| one_smul _ _

/-- Any invertible action preserves the non-zeroness of rays. This is primarily of interest when
`G = Rˣ` -/
instance : MulAction G (Module.Ray R M) where
  smul := fun r => Quotientₓ.map ((· • ·) r) fun a b => SameRay.smul _
  mul_smul := fun a b => Quotientₓ.ind fun m => congr_argₓ Quotientₓ.mk <| mul_smul a b _
  one_smul := Quotientₓ.ind fun m => congr_argₓ Quotientₓ.mk <| one_smul _ _

/-- The action via `linear_equiv.apply_distrib_mul_action` corresponds to `module.ray.map`. -/
@[simp]
theorem Module.Ray.linear_equiv_smul_eq_map (e : M ≃ₗ[R] M) (v : Module.Ray R M) : e • v = Module.Ray.map e v :=
  rfl

@[simp]
theorem smul_ray_of_ne_zero (g : G) (v : M) hv :
    g • rayOfNeZero R v hv = rayOfNeZero R (g • v) ((smul_ne_zero_iff_ne _).2 hv) :=
  rfl

end Action

namespace Module.Ray

/-- Scaling by a positive unit is a no-op. -/
theorem units_smul_of_pos [Nontrivial R] (u : (R)ˣ) (hu : 0 < (u : R)) (v : Module.Ray R M) : u • v = v := by
  induction v using Module.Ray.ind
  rw [smul_ray_of_ne_zero, ray_eq_iff]
  exact same_ray_pos_smul_left _ hu

/-- An arbitrary `ray_vector` giving a ray. -/
def some_ray_vector [Nontrivial R] (x : Module.Ray R M) : RayVector M :=
  Quotientₓ.out x

/-- The ray of `some_ray_vector`. -/
@[simp]
theorem some_ray_vector_ray [Nontrivial R] (x : Module.Ray R M) : (⟦x.some_ray_vector⟧ : Module.Ray R M) = x :=
  Quotientₓ.out_eq _

/-- An arbitrary nonzero vector giving a ray. -/
def some_vector [Nontrivial R] (x : Module.Ray R M) : M :=
  x.some_ray_vector

/-- `some_vector` is nonzero. -/
@[simp]
theorem some_vector_ne_zero [Nontrivial R] (x : Module.Ray R M) : x.some_vector ≠ 0 :=
  x.some_ray_vector.property

/-- The ray of `some_vector`. -/
@[simp]
theorem some_vector_ray [Nontrivial R] (x : Module.Ray R M) : rayOfNeZero R _ x.some_vector_ne_zero = x :=
  (congr_argₓ _ (Subtype.coe_eta _ _) : _).trans x.out_eq

end Module.Ray

end OrderedCommSemiring

section OrderedCommRing

attribute [local instance] RayVector.sameRaySetoid

variable {R : Type _} [OrderedCommRing R]

variable {M N : Type _} [AddCommGroupₓ M] [AddCommGroupₓ N] [Module R M] [Module R N]

/-- If two vectors are in the same ray, so are their negations. -/
theorem SameRay.neg {v₁ v₂ : M} : SameRay R v₁ v₂ → SameRay R (-v₁) (-v₂) := fun ⟨r₁, r₂, hr₁, hr₂, h⟩ =>
  ⟨r₁, r₂, hr₁, hr₂, by
    rwa [smul_neg, smul_neg, neg_inj]⟩

/-- `same_ray.neg` as an `iff`. -/
@[simp]
theorem same_ray_neg_iff {v₁ v₂ : M} : SameRay R (-v₁) (-v₂) ↔ SameRay R v₁ v₂ :=
  ⟨fun h => by
    simpa only [neg_negₓ] using h.neg, SameRay.neg⟩

theorem same_ray_neg_swap {v₁ v₂ : M} : SameRay R (-v₁) v₂ ↔ SameRay R v₁ (-v₂) :=
  ⟨fun h => by
    simpa only [neg_negₓ] using h.neg, fun h => by
    simpa only [neg_negₓ] using h.neg⟩

/-- If a vector is in the same ray as its negation, that vector is zero. -/
theorem eq_zero_of_same_ray_self_neg [NoZeroSmulDivisors R M] {v₁ : M} (h : SameRay R v₁ (-v₁)) : v₁ = 0 := by
  rcases h with ⟨r₁, r₂, hr₁, hr₂, h⟩
  rw [smul_neg, ← neg_smul, ← sub_eq_zero, ← sub_smul, sub_neg_eq_add, smul_eq_zero] at h
  exact h.resolve_left (add_pos hr₁ hr₂).ne'

namespace RayVector

variable {R}

/-- Negating a nonzero vector. -/
instance : Neg (RayVector M) :=
  ⟨fun v => ⟨-v, neg_ne_zero.2 v.prop⟩⟩

/-- Negating a nonzero vector commutes with coercion to the underlying module. -/
@[simp, norm_cast]
theorem coe_neg (v : RayVector M) : ↑(-v) = -(v : M) :=
  rfl

/-- Negating a nonzero vector twice produces the original vector. -/
@[simp]
protected theorem neg_negₓ (v : RayVector M) : - -v = v := by
  rw [Subtype.ext_iff, coe_neg, coe_neg, neg_negₓ]

variable (R)

/-- If two nonzero vectors are equivalent, so are their negations. -/
@[simp]
theorem equiv_neg_iff [Nontrivial R] (v₁ v₂ : RayVector M) : -v₁ ≈ -v₂ ↔ v₁ ≈ v₂ := by
  rw [equiv_iff_same_ray, equiv_iff_same_ray, coe_neg, coe_neg, same_ray_neg_iff]

end RayVector

variable (R)

/-- Negating a ray. -/
instance [Nontrivial R] : Neg (Module.Ray R M) :=
  ⟨Quotientₓ.map (fun v => -v) fun v₁ v₂ => (RayVector.equiv_neg_iff R v₁ v₂).2⟩

/-- The ray given by the negation of a nonzero vector. -/
theorem ray_neg [Nontrivial R] (v : M) (h : v ≠ 0) :
    rayOfNeZero R _
        (show -v ≠ 0 by
          rw [neg_ne_zero] <;> exact h) =
      -rayOfNeZero R _ h :=
  rfl

namespace Module.Ray

variable {R}

/-- Negating a ray twice produces the original ray. -/
@[simp]
protected theorem neg_negₓ [Nontrivial R] (x : Module.Ray R M) : - -x = x :=
  Quotientₓ.ind (fun a => congr_argₓ Quotientₓ.mk <| RayVector.neg_neg _) x

variable (R M)

/-- Negating a ray is involutive. -/
theorem neg_involutive [Nontrivial R] : Function.Involutive fun x : Module.Ray R M => -x := fun x =>
  Module.Ray.neg_neg x

variable {R M}

protected theorem eq_neg_iff_eq_neg [Nontrivial R] (x y : Module.Ray R M) : x = -y ↔ y = -x := by
  rw [← Module.Ray.neg_neg x, (neg_involutive R M).Injective.eq_iff, Module.Ray.neg_neg x, eq_comm]

/-- A ray does not equal its own negation. -/
theorem ne_neg_self [Nontrivial R] [NoZeroSmulDivisors R M] (x : Module.Ray R M) : x ≠ -x := by
  intro h
  induction x using Module.Ray.ind
  rw [← ray_neg, ray_eq_iff] at h
  exact x_hv (eq_zero_of_same_ray_self_neg h)

/-- Scaling by a negative unit is negation. -/
theorem units_smul_of_neg [Nontrivial R] (u : (R)ˣ) (hu : (u : R) < 0) (v : Module.Ray R M) : u • v = -v := by
  induction v using Module.Ray.ind
  rw [smul_ray_of_ne_zero, ← ray_neg, ray_eq_iff, ← same_ray_neg_swap, Units.smul_def, ← neg_smul]
  exact same_ray_pos_smul_left _ (neg_pos_of_neg hu)

end Module.Ray

namespace Basis

variable {R} {ι : Type _} [Fintype ι] [DecidableEq ι]

/-- The orientation given by a basis. -/
protected def Orientation [Nontrivial R] (e : Basis ι R M) : Orientation R M ι :=
  rayOfNeZero R _ e.det_ne_zero

theorem orientation_map [Nontrivial R] (e : Basis ι R M) (f : M ≃ₗ[R] N) :
    (e.map f).Orientation = Orientation.map ι f e.orientation := by
  simp_rw [Basis.orientation, Orientation.map_apply, Basis.det_map']

/-- The value of `orientation.map` when the index type has the cardinality of a basis, in terms
of `f.det`. -/
theorem map_orientation_eq_det_inv_smul [Nontrivial R] [IsDomain R] (e : Basis ι R M) (x : Orientation R M ι)
    (f : M ≃ₗ[R] M) : Orientation.map ι f x = f.det⁻¹ • x := by
  induction' x using Module.Ray.ind with g hg
  rw [Orientation.map_apply, smul_ray_of_ne_zero, ray_eq_iff, Units.smul_def,
    (g.comp_linear_map ↑f.symm).eq_smul_basis_det e, g.eq_smul_basis_det e, AlternatingMap.comp_linear_map_apply,
    AlternatingMap.smul_apply, Basis.det_comp, Basis.det_self, mul_oneₓ, smul_eq_mul, mul_comm, mul_smul,
    LinearEquiv.coe_inv_det]

/-- The orientation given by a basis derived using `units_smul`, in terms of the product of those
units. -/
theorem orientation_units_smul [Nontrivial R] (e : Basis ι R M) (w : ι → Units R) :
    (e.units_smul w).Orientation = (∏ i, w i)⁻¹ • e.orientation := by
  rw [Basis.orientation, Basis.orientation, smul_ray_of_ne_zero, ray_eq_iff, e.det.eq_smul_basis_det (e.units_smul w),
    det_units_smul, Units.smul_def, smul_smul]
  norm_cast
  simp

end Basis

end OrderedCommRing

section LinearOrderedCommRing

variable {R : Type _} [LinearOrderedCommRing R]

variable {M : Type _} [AddCommGroupₓ M] [Module R M]

variable {ι : Type _} [DecidableEq ι]

/-- `same_ray` follows from membership of `mul_action.orbit` for the `units.pos_subgroup`. -/
theorem same_ray_of_mem_orbit {v₁ v₂ : M} (h : v₁ ∈ MulAction.Orbit (Units.posSubgroup R) v₂) : SameRay R v₁ v₂ := by
  rcases h with ⟨⟨r, hr⟩, rfl : r • v₂ = v₁⟩
  exact same_ray_pos_smul_left _ hr

/-- Scaling by an inverse unit is the same as scaling by itself. -/
@[simp]
theorem units_inv_smul (u : (R)ˣ) (v : Module.Ray R M) : u⁻¹ • v = u • v := by
  induction' v using Module.Ray.ind with v hv
  rw [smul_ray_of_ne_zero, smul_ray_of_ne_zero, ray_eq_iff]
  have : ∀ {u : (R)ˣ}, 0 < (u : R) → SameRay R (u⁻¹ • v) (u • v) := fun u h =>
    ((SameRay.refl v).pos_smul_left <| units.inv_pos.mpr h).pos_smul_right h
  cases lt_or_lt_iff_ne.2 u.ne_zero
  · rw [← Units.neg_neg u, Units.neg_inv, (-u).neg_smul, Units.neg_smul]
    refine' (this _).neg
    exact neg_pos_of_neg h
    
  · exact this h
    

section

variable [NoZeroSmulDivisors R M]

/-- A nonzero vector is in the same ray as a multiple of itself if and only if that multiple
is positive. -/
@[simp]
theorem same_ray_smul_right_iff {v : M} (hv : v ≠ 0) (r : R) : SameRay R v (r • v) ↔ 0 < r := by
  constructor
  · rintro ⟨r₁, r₂, hr₁, hr₂, h⟩
    rw [smul_smul, ← sub_eq_zero, ← sub_smul, sub_eq_add_neg, neg_mul_eq_mul_neg] at h
    by_contra hr
    rw [not_ltₓ, ← neg_le_neg_iff, neg_zero] at hr
    have hzzz := ne_of_gtₓ (add_pos_of_pos_of_nonneg hr₁ (mul_nonneg hr₂.le hr))
    simpa [ne_of_gtₓ (add_pos_of_pos_of_nonneg hr₁ (mul_nonneg hr₂.le hr)), -mul_neg_eq_neg_mul_symm] using h
    
  · exact fun h => same_ray_pos_smul_right v h
    

/-- A multiple of a nonzero vector is in the same ray as that vector if and only if that multiple
is positive. -/
@[simp]
theorem same_ray_smul_left_iff {v : M} (hv : v ≠ 0) (r : R) : SameRay R (r • v) v ↔ 0 < r := by
  rw [same_ray_comm]
  exact same_ray_smul_right_iff hv r

/-- The negation of a nonzero vector is in the same ray as a multiple of that vector if and
only if that multiple is negative. -/
@[simp]
theorem same_ray_neg_smul_right_iff {v : M} (hv : v ≠ 0) (r : R) : SameRay R (-v) (r • v) ↔ r < 0 := by
  rw [← same_ray_neg_iff, neg_negₓ, ← neg_smul, same_ray_smul_right_iff hv (-r)]
  exact Right.neg_pos_iff

/-- A multiple of a nonzero vector is in the same ray as the negation of that vector if and
only if that multiple is negative. -/
@[simp]
theorem same_ray_neg_smul_left_iff {v : M} (hv : v ≠ 0) (r : R) : SameRay R (r • v) (-v) ↔ r < 0 := by
  rw [← same_ray_neg_iff, neg_negₓ, ← neg_smul, same_ray_smul_left_iff hv (-r)]
  exact Left.neg_pos_iff

/-- A nonzero vector is in the same ray as a multiple of itself if and only if that multiple
is positive. -/
@[simp]
theorem units_smul_eq_self_iff {u : (R)ˣ} {v : Module.Ray R M} : u • v = v ↔ (0 : R) < u := by
  induction' v using Module.Ray.ind with v hv
  rw [smul_ray_of_ne_zero, ray_eq_iff, Units.smul_def]
  exact same_ray_smul_left_iff hv _

/-- A nonzero vector is in the same ray as a multiple of itself if and only if that multiple
is positive. -/
@[simp]
theorem units_smul_eq_neg_iff {u : (R)ˣ} {v : Module.Ray R M} : u • v = -v ↔ ↑u < (0 : R) := by
  induction' v using Module.Ray.ind with v hv
  rw [smul_ray_of_ne_zero, ← ray_neg, ray_eq_iff, Units.smul_def]
  exact same_ray_neg_smul_left_iff hv _

end

namespace Basis

variable [Fintype ι]

/-- The orientations given by two bases are equal if and only if the determinant of one basis
with respect to the other is positive. -/
theorem orientation_eq_iff_det_pos (e₁ e₂ : Basis ι R M) : e₁.orientation = e₂.orientation ↔ 0 < e₁.det e₂ := by
  rw [Basis.orientation, Basis.orientation, ray_eq_iff, e₁.det.eq_smul_basis_det e₂, AlternatingMap.smul_apply,
    Basis.det_self, smul_eq_mul, mul_oneₓ, same_ray_smul_left_iff e₂.det_ne_zero (_ : R)]

/-- Given a basis, any orientation equals the orientation given by that basis or its negation. -/
theorem orientation_eq_or_eq_neg (e : Basis ι R M) (x : Orientation R M ι) : x = e.orientation ∨ x = -e.orientation :=
  by
  induction' x using Module.Ray.ind with x hx
  rw [Basis.orientation, ray_eq_iff, ← ray_neg, ray_eq_iff, x.eq_smul_basis_det e,
    same_ray_neg_smul_left_iff e.det_ne_zero (_ : R), same_ray_smul_left_iff e.det_ne_zero (_ : R), lt_or_lt_iff_ne,
    ne_comm, AlternatingMap.map_basis_ne_zero_iff]
  exact hx

/-- Given a basis, an orientation equals the negation of that given by that basis if and only
if it does not equal that given by that basis. -/
theorem orientation_ne_iff_eq_neg (e : Basis ι R M) (x : Orientation R M ι) : x ≠ e.orientation ↔ x = -e.orientation :=
  ⟨fun h => (e.orientation_eq_or_eq_neg x).resolve_left h, fun h =>
    h.symm ▸ (Module.Ray.ne_neg_self e.orientation).symm⟩

/-- Composing a basis with a linear equiv gives the same orientation if and only if the
determinant is positive. -/
theorem orientation_comp_linear_equiv_eq_iff_det_pos (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).Orientation = e.orientation ↔ 0 < (f : M →ₗ[R] M).det := by
  rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_self_iff, LinearEquiv.coe_det]

/-- Composing a basis with a linear equiv gives the negation of that orientation if and only if
the determinant is negative. -/
theorem orientation_comp_linear_equiv_eq_neg_iff_det_neg (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).Orientation = -e.orientation ↔ (f : M →ₗ[R] M).det < 0 := by
  rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_neg_iff, LinearEquiv.coe_det]

/-- Negating a single basis vector (represented using `units_smul`) negates the corresponding
orientation. -/
@[simp]
theorem orientation_neg_single [Nontrivial R] (e : Basis ι R M) (i : ι) :
    (e.units_smul (Function.update 1 i (-1))).Orientation = -e.orientation := by
  rw [orientation_units_smul, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

/-- Given a basis and an orientation, return a basis giving that orientation: either the original
basis, or one constructed by negating a single (arbitrary) basis vector. -/
def adjust_to_orientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι) : Basis ι R M :=
  have := Classical.decEq (Orientation R M ι)
  if e.orientation = x then e else e.units_smul (Function.update 1 (Classical.arbitrary ι) (-1))

/-- `adjust_to_orientation` gives a basis with the required orientation. -/
@[simp]
theorem orientation_adjust_to_orientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι) :
    (e.adjust_to_orientation x).Orientation = x := by
  rw [adjust_to_orientation]
  split_ifs with h
  · exact h
    
  · rw [orientation_neg_single, eq_comm, ← orientation_ne_iff_eq_neg, ne_comm]
    exact h
    

/-- Every basis vector from `adjust_to_orientation` is either that from the original basis or its
negation. -/
theorem adjust_to_orientation_apply_eq_or_eq_neg [Nontrivial R] [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι)
    (i : ι) : e.adjust_to_orientation x i = e i ∨ e.adjust_to_orientation x i = -e i := by
  rw [adjust_to_orientation]
  split_ifs with h
  · simp
    
  · by_cases' hi : i = Classical.arbitrary ι <;> simp [units_smul_apply, hi]
    

end Basis

end LinearOrderedCommRing

section LinearOrderedField

variable (R : Type _) [LinearOrderedField R]

variable {M : Type _} [AddCommGroupₓ M] [Module R M]

variable {ι : Type _} [DecidableEq ι]

/-- `same_ray` is equivalent to membership of `mul_action.orbit` for the `units.pos_subgroup`. -/
theorem same_ray_iff_mem_orbit (v₁ v₂ : M) : SameRay R v₁ v₂ ↔ v₁ ∈ MulAction.Orbit (Units.posSubgroup R) v₂ := by
  constructor
  · rintro ⟨r₁, r₂, hr₁, hr₂, h⟩
    rw [MulAction.mem_orbit_iff]
    have h' : (r₁⁻¹ * r₂) • v₂ = v₁ := by
      rw [mul_smul, ← h, ← mul_smul, inv_mul_cancel (ne_of_ltₓ hr₁).symm, one_smul]
    have hr' : 0 < r₁⁻¹ * r₂ := mul_pos (inv_pos.2 hr₁) hr₂
    change (⟨Units.mk0 (r₁⁻¹ * r₂) (ne_of_ltₓ hr').symm, hr'⟩ : Units.posSubgroup R) • v₂ = v₁ at h'
    exact ⟨_, h'⟩
    
  · exact same_ray_of_mem_orbit
    

/-- `same_ray_setoid` equals `mul_action.orbit_rel` for the `units.pos_subgroup`. -/
theorem same_ray_setoid_eq_orbit_rel : sameRaySetoid R M = MulAction.orbitRel (Units.posSubgroup R) M :=
  Setoidₓ.ext' <| same_ray_iff_mem_orbit R

variable {R}

namespace Orientation

variable [Fintype ι] [FiniteDimensional R M]

open FiniteDimensional

/-- If the index type has cardinality equal to the finite dimension, any two orientations are
equal or negations. -/
theorem eq_or_eq_neg (x₁ x₂ : Orientation R M ι) (h : Fintype.card ι = finrank R M) : x₁ = x₂ ∨ x₁ = -x₂ := by
  have e := (fin_basis R M).reindex (Fintype.equivFinOfCardEq h).symm
  rcases e.orientation_eq_or_eq_neg x₁ with (h₁ | h₁) <;>
    rcases e.orientation_eq_or_eq_neg x₂ with (h₂ | h₂) <;> simp [h₁, h₂]

/-- If the index type has cardinality equal to the finite dimension, an orientation equals the
negation of another orientation if and only if they are not equal. -/
theorem ne_iff_eq_neg (x₁ x₂ : Orientation R M ι) (h : Fintype.card ι = finrank R M) : x₁ ≠ x₂ ↔ x₁ = -x₂ :=
  ⟨fun hn => (eq_or_eq_neg x₁ x₂ h).resolve_left hn, fun he => he.symm ▸ (Module.Ray.ne_neg_self x₂).symm⟩

/-- The value of `orientation.map` when the index type has cardinality equal to the finite
dimension, in terms of `f.det`. -/
theorem map_eq_det_inv_smul (x : Orientation R M ι) (f : M ≃ₗ[R] M) (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = f.det⁻¹ • x :=
  have e := (fin_basis R M).reindex (Fintype.equivFinOfCardEq h).symm
  e.map_orientation_eq_det_inv_smul x f

/-- If the index type has cardinality equal to the finite dimension, composing an alternating
map with the same linear equiv on each argument gives the same orientation if and only if the
determinant is positive. -/
theorem map_eq_iff_det_pos (x : Orientation R M ι) (f : M ≃ₗ[R] M) (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = x ↔ 0 < (f : M →ₗ[R] M).det := by
  rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_self_iff, LinearEquiv.coe_det]

/-- If the index type has cardinality equal to the finite dimension, composing an alternating
map with the same linear equiv on each argument gives the negation of that orientation if and
only if the determinant is negative. -/
theorem map_eq_neg_iff_det_neg (x : Orientation R M ι) (f : M ≃ₗ[R] M) (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = -x ↔ (f : M →ₗ[R] M).det < 0 := by
  rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_neg_iff, LinearEquiv.coe_det]

/-- If the index type has cardinality equal to the finite dimension, a basis with the given
orientation. -/
def some_basis [Nonempty ι] (x : Orientation R M ι) (h : Fintype.card ι = finrank R M) : Basis ι R M :=
  ((fin_basis R M).reindex (Fintype.equivFinOfCardEq h).symm).adjustToOrientation x

/-- `some_basis` gives a basis with the required orientation. -/
@[simp]
theorem some_basis_orientation [Nonempty ι] (x : Orientation R M ι) (h : Fintype.card ι = finrank R M) :
    (x.some_basis h).Orientation = x :=
  Basis.orientation_adjust_to_orientation _ _

end Orientation

end LinearOrderedField

