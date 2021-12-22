import Mathbin.Analysis.NormedSpace.AddTorsor
import Mathbin.Analysis.NormedSpace.LinearIsometry

/-!
# Affine isometries

In this file we define `affine_isometry 𝕜 P P₂` to be an affine isometric embedding of normed
add-torsors `P` into `P₂` over normed `𝕜`-spaces and `affine_isometry_equiv` to be an affine
isometric equivalence between `P` and `P₂`.

We also prove basic lemmas and provide convenience constructors.  The choice of these lemmas and
constructors is closely modelled on those for the `linear_isometry` and `affine_map` theories.

Since many elementary properties don't require `∥x∥ = 0 → x = 0` we initially set up the theory for
`semi_normed_add_torsor` and specialize to `normed_add_torsor` only when needed.

## Notation

We introduce the notation `P →ᵃⁱ[𝕜] P₂` for `affine_isometry 𝕜 P P₂`, and `P ≃ᵃⁱ[𝕜] P₂` for
`affine_isometry_equiv 𝕜 P P₂`.  In contrast with the notation `→ₗᵢ` for linear isometries, `≃ᵢ`
for isometric equivalences, etc., the "i" here is a superscript.  This is for aesthetic reasons to
match the superscript "a" (note that in mathlib `→ᵃ` is an affine map, since `→ₐ` has been taken by
algebra-homomorphisms.)

-/


open Function Set

variable (𝕜 : Type _) {V V₁ V₂ V₃ V₄ : Type _} {P₁ : Type _} (P P₂ : Type _) {P₃ P₄ : Type _} [NormedField 𝕜]
  [SemiNormedGroup V] [NormedGroup V₁] [SemiNormedGroup V₂] [SemiNormedGroup V₃] [SemiNormedGroup V₄]
  [SemiNormedSpace 𝕜 V] [NormedSpace 𝕜 V₁] [SemiNormedSpace 𝕜 V₂] [SemiNormedSpace 𝕜 V₃] [SemiNormedSpace 𝕜 V₄]
  [PseudoMetricSpace P] [MetricSpace P₁] [PseudoMetricSpace P₂] [PseudoMetricSpace P₃] [PseudoMetricSpace P₄]
  [SemiNormedAddTorsor V P] [NormedAddTorsor V₁ P₁] [SemiNormedAddTorsor V₂ P₂] [SemiNormedAddTorsor V₃ P₃]
  [SemiNormedAddTorsor V₄ P₄]

include V V₂

/--  An `𝕜`-affine isometric embedding of one normed add-torsor over a normed `𝕜`-space into
another. -/
structure AffineIsometry extends P →ᵃ[𝕜] P₂ where
  norm_map : ∀ x : V, ∥linear x∥ = ∥x∥

omit V V₂

variable {𝕜 P P₂}

notation:25 P " →ᵃⁱ[" 𝕜:25 "] " P₂:0 => AffineIsometry 𝕜 P P₂

namespace AffineIsometry

variable (f : P →ᵃⁱ[𝕜] P₂)

/--  The underlying linear map of an affine isometry is in fact a linear isometry. -/
protected def LinearIsometry : V →ₗᵢ[𝕜] V₂ :=
  { f.linear with norm_map' := f.norm_map }

@[simp]
theorem linear_eq_linear_isometry : f.linear = f.linear_isometry.to_linear_map := by
  ext
  rfl

include V V₂

instance : CoeFun (P →ᵃⁱ[𝕜] P₂) fun _ => P → P₂ :=
  ⟨fun f => f.to_fun⟩

omit V V₂

@[simp]
theorem coe_to_affine_map : ⇑f.to_affine_map = f :=
  rfl

include V V₂

theorem to_affine_map_injective : injective (to_affine_map : (P →ᵃⁱ[𝕜] P₂) → P →ᵃ[𝕜] P₂)
  | ⟨f, _⟩, ⟨g, _⟩, rfl => rfl

theorem coe_fn_injective : @injective (P →ᵃⁱ[𝕜] P₂) (P → P₂) coeFn :=
  AffineMap.coe_fn_injective.comp to_affine_map_injective

@[ext]
theorem ext {f g : P →ᵃⁱ[𝕜] P₂} (h : ∀ x, f x = g x) : f = g :=
  coe_fn_injective $ funext h

omit V V₂

end AffineIsometry

namespace LinearIsometry

variable (f : V →ₗᵢ[𝕜] V₂)

/--  Reinterpret a linear isometry as an affine isometry. -/
def to_affine_isometry : V →ᵃⁱ[𝕜] V₂ :=
  { f.to_linear_map.to_affine_map with norm_map := f.norm_map }

@[simp]
theorem coe_to_affine_isometry : ⇑(f.to_affine_isometry : V →ᵃⁱ[𝕜] V₂) = f :=
  rfl

@[simp]
theorem to_affine_isometry_linear_isometry : f.to_affine_isometry.linear_isometry = f := by
  ext
  rfl

@[simp]
theorem to_affine_isometry_to_affine_map : f.to_affine_isometry.to_affine_map = f.to_linear_map.to_affine_map :=
  rfl

end LinearIsometry

namespace AffineIsometry

variable (f : P →ᵃⁱ[𝕜] P₂) (f₁ : P₁ →ᵃⁱ[𝕜] P₂)

@[simp]
theorem map_vadd (p : P) (v : V) : f (v +ᵥ p) = f.linear_isometry v +ᵥ f p :=
  f.to_affine_map.map_vadd p v

@[simp]
theorem map_vsub (p1 p2 : P) : f.linear_isometry (p1 -ᵥ p2) = f p1 -ᵥ f p2 :=
  f.to_affine_map.linear_map_vsub p1 p2

@[simp]
theorem dist_map (x y : P) : dist (f x) (f y) = dist x y := by
  rw [dist_eq_norm_vsub V₂, dist_eq_norm_vsub V, ← map_vsub, f.linear_isometry.norm_map]

@[simp]
theorem nndist_map (x y : P) : nndist (f x) (f y) = nndist x y := by
  simp [nndist_dist]

@[simp]
theorem edist_map (x y : P) : edist (f x) (f y) = edist x y := by
  simp [edist_dist]

protected theorem Isometry : Isometry f :=
  f.edist_map

protected theorem injective : injective f₁ :=
  f₁.isometry.injective

@[simp]
theorem map_eq_iff {x y : P₁} : f₁ x = f₁ y ↔ x = y :=
  f₁.injective.eq_iff

theorem map_ne {x y : P₁} (h : x ≠ y) : f₁ x ≠ f₁ y :=
  f₁.injective.ne h

protected theorem lipschitz : LipschitzWith 1 f :=
  f.isometry.lipschitz

protected theorem antilipschitz : AntilipschitzWith 1 f :=
  f.isometry.antilipschitz

@[continuity]
protected theorem Continuous : Continuous f :=
  f.isometry.continuous

theorem ediam_image (s : Set P) : Emetric.diam (f '' s) = Emetric.diam s :=
  f.isometry.ediam_image s

theorem ediam_range : Emetric.diam (range f) = Emetric.diam (univ : Set P) :=
  f.isometry.ediam_range

theorem diam_image (s : Set P) : Metric.diam (f '' s) = Metric.diam s :=
  f.isometry.diam_image s

theorem diam_range : Metric.diam (range f) = Metric.diam (univ : Set P) :=
  f.isometry.diam_range

@[simp]
theorem comp_continuous_iff {α : Type _} [TopologicalSpace α] {g : α → P} : Continuous (f ∘ g) ↔ Continuous g :=
  f.isometry.comp_continuous_iff

include V

/--  The identity affine isometry. -/
def id : P →ᵃⁱ[𝕜] P :=
  ⟨AffineMap.id 𝕜 P, fun x => rfl⟩

@[simp]
theorem coe_id : ⇑(id : P →ᵃⁱ[𝕜] P) = _root_.id :=
  rfl

@[simp]
theorem id_apply (x : P) : (AffineIsometry.id : P →ᵃⁱ[𝕜] P) x = x :=
  rfl

@[simp]
theorem id_to_affine_map : (id.toAffineMap : P →ᵃ[𝕜] P) = AffineMap.id 𝕜 P :=
  rfl

instance : Inhabited (P →ᵃⁱ[𝕜] P) :=
  ⟨id⟩

include V₂ V₃

/--  Composition of affine isometries. -/
def comp (g : P₂ →ᵃⁱ[𝕜] P₃) (f : P →ᵃⁱ[𝕜] P₂) : P →ᵃⁱ[𝕜] P₃ :=
  ⟨g.to_affine_map.comp f.to_affine_map, fun x => (g.norm_map _).trans (f.norm_map _)⟩

@[simp]
theorem coe_comp (g : P₂ →ᵃⁱ[𝕜] P₃) (f : P →ᵃⁱ[𝕜] P₂) : ⇑g.comp f = (g ∘ f) :=
  rfl

omit V V₂ V₃

@[simp]
theorem id_comp : (id : P₂ →ᵃⁱ[𝕜] P₂).comp f = f :=
  ext $ fun x => rfl

@[simp]
theorem comp_id : f.comp id = f :=
  ext $ fun x => rfl

include V V₂ V₃ V₄

theorem comp_assoc (f : P₃ →ᵃⁱ[𝕜] P₄) (g : P₂ →ᵃⁱ[𝕜] P₃) (h : P →ᵃⁱ[𝕜] P₂) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

omit V₂ V₃ V₄

instance : Monoidₓ (P →ᵃⁱ[𝕜] P) where
  one := id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]
theorem coe_one : ⇑(1 : P →ᵃⁱ[𝕜] P) = _root_.id :=
  rfl

@[simp]
theorem coe_mul (f g : P →ᵃⁱ[𝕜] P) : (⇑f*g) = (f ∘ g) :=
  rfl

end AffineIsometry

variable (𝕜 P P₂)

include V V₂

/--  A affine isometric equivalence between two normed vector spaces. -/
structure AffineIsometryEquiv extends P ≃ᵃ[𝕜] P₂ where
  norm_map : ∀ x, ∥linear x∥ = ∥x∥

variable {𝕜 P P₂}

omit V V₂

notation:25 P " ≃ᵃⁱ[" 𝕜:25 "] " P₂:0 => AffineIsometryEquiv 𝕜 P P₂

namespace AffineIsometryEquiv

variable (e : P ≃ᵃⁱ[𝕜] P₂)

/--  The underlying linear equiv of an affine isometry equiv is in fact a linear isometry equiv. -/
protected def LinearIsometryEquiv : V ≃ₗᵢ[𝕜] V₂ :=
  { e.linear with norm_map' := e.norm_map }

@[simp]
theorem linear_eq_linear_isometry : e.linear = e.linear_isometry_equiv.to_linear_equiv := by
  ext
  rfl

include V V₂

instance : CoeFun (P ≃ᵃⁱ[𝕜] P₂) fun _ => P → P₂ :=
  ⟨fun f => f.to_fun⟩

@[simp]
theorem coe_mk (e : P ≃ᵃ[𝕜] P₂) (he : ∀ x, ∥e.linear x∥ = ∥x∥) : ⇑mk e he = e :=
  rfl

@[simp]
theorem coe_to_affine_equiv (e : P ≃ᵃⁱ[𝕜] P₂) : ⇑e.to_affine_equiv = e :=
  rfl

theorem to_affine_equiv_injective : injective (to_affine_equiv : (P ≃ᵃⁱ[𝕜] P₂) → P ≃ᵃ[𝕜] P₂)
  | ⟨e, _⟩, ⟨_, _⟩, rfl => rfl

@[ext]
theorem ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : ∀ x, e x = e' x) : e = e' :=
  to_affine_equiv_injective $ AffineEquiv.ext h

omit V V₂

/--  Reinterpret a `affine_isometry_equiv` as a `affine_isometry`. -/
def to_affine_isometry : P →ᵃⁱ[𝕜] P₂ :=
  ⟨e.1.toAffineMap, e.2⟩

@[simp]
theorem coe_to_affine_isometry : ⇑e.to_affine_isometry = e :=
  rfl

/--  Construct an affine isometry equivalence by verifying the relation between the map and its
linear part at one base point. Namely, this function takes a map `e : P₁ → P₂`, a linear isometry
equivalence `e' : V₁ ≃ᵢₗ[k] V₂`, and a point `p` such that for any other point `p'` we have
`e p' = e' (p' -ᵥ p) +ᵥ e p`. -/
def mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p : P₁) (h : ∀ p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p) : P₁ ≃ᵃⁱ[𝕜] P₂ :=
  { AffineEquiv.mk' e e'.to_linear_equiv p h with norm_map := e'.norm_map }

@[simp]
theorem coe_mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) p h : ⇑mk' e e' p h = e :=
  rfl

@[simp]
theorem linear_isometry_equiv_mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) p h : (mk' e e' p h).LinearIsometryEquiv = e' := by
  ext
  rfl

end AffineIsometryEquiv

namespace LinearIsometryEquiv

variable (e : V ≃ₗᵢ[𝕜] V₂)

/--  Reinterpret a linear isometry equiv as an affine isometry equiv. -/
def to_affine_isometry_equiv : V ≃ᵃⁱ[𝕜] V₂ :=
  { e.to_linear_equiv.to_affine_equiv with norm_map := e.norm_map }

@[simp]
theorem coe_to_affine_isometry_equiv : ⇑(e.to_affine_isometry_equiv : V ≃ᵃⁱ[𝕜] V₂) = e :=
  rfl

@[simp]
theorem to_affine_isometry_equiv_linear_isometry_equiv : e.to_affine_isometry_equiv.linear_isometry_equiv = e := by
  ext
  rfl

@[simp]
theorem to_affine_isometry_equiv_to_affine_equiv :
    e.to_affine_isometry_equiv.to_affine_equiv = e.to_linear_equiv.to_affine_equiv :=
  rfl

@[simp]
theorem to_affine_isometry_equiv_to_affine_isometry :
    e.to_affine_isometry_equiv.to_affine_isometry = e.to_linear_isometry.to_affine_isometry :=
  rfl

end LinearIsometryEquiv

namespace AffineIsometryEquiv

variable (e : P ≃ᵃⁱ[𝕜] P₂)

protected theorem Isometry : Isometry e :=
  e.to_affine_isometry.isometry

/--  Reinterpret a `affine_isometry_equiv` as an `isometric`. -/
def to_isometric : P ≃ᵢ P₂ :=
  ⟨e.to_affine_equiv.to_equiv, e.isometry⟩

@[simp]
theorem coe_to_isometric : ⇑e.to_isometric = e :=
  rfl

include V V₂

theorem range_eq_univ (e : P ≃ᵃⁱ[𝕜] P₂) : Set.Range e = Set.Univ := by
  rw [← coe_to_isometric]
  exact Isometric.range_eq_univ _

omit V V₂

/--  Reinterpret a `affine_isometry_equiv` as an `homeomorph`. -/
def to_homeomorph : P ≃ₜ P₂ :=
  e.to_isometric.to_homeomorph

@[simp]
theorem coe_to_homeomorph : ⇑e.to_homeomorph = e :=
  rfl

protected theorem Continuous : Continuous e :=
  e.isometry.continuous

protected theorem ContinuousAt {x} : ContinuousAt e x :=
  e.continuous.continuous_at

protected theorem ContinuousOn {s} : ContinuousOn e s :=
  e.continuous.continuous_on

protected theorem ContinuousWithinAt {s x} : ContinuousWithinAt e s x :=
  e.continuous.continuous_within_at

variable (𝕜 P)

include V

/--  Identity map as a `affine_isometry_equiv`. -/
def refl : P ≃ᵃⁱ[𝕜] P :=
  ⟨AffineEquiv.refl 𝕜 P, fun x => rfl⟩

variable {𝕜 P}

instance : Inhabited (P ≃ᵃⁱ[𝕜] P) :=
  ⟨refl 𝕜 P⟩

@[simp]
theorem coe_refl : ⇑refl 𝕜 P = id :=
  rfl

@[simp]
theorem to_affine_equiv_refl : (refl 𝕜 P).toAffineEquiv = AffineEquiv.refl 𝕜 P :=
  rfl

@[simp]
theorem to_isometric_refl : (refl 𝕜 P).toIsometric = Isometric.refl P :=
  rfl

@[simp]
theorem to_homeomorph_refl : (refl 𝕜 P).toHomeomorph = Homeomorph.refl P :=
  rfl

omit V

/--  The inverse `affine_isometry_equiv`. -/
def symm : P₂ ≃ᵃⁱ[𝕜] P :=
  { e.to_affine_equiv.symm with norm_map := e.linear_isometry_equiv.symm.norm_map }

@[simp]
theorem apply_symm_apply (x : P₂) : e (e.symm x) = x :=
  e.to_affine_equiv.apply_symm_apply x

@[simp]
theorem symm_apply_apply (x : P) : e.symm (e x) = x :=
  e.to_affine_equiv.symm_apply_apply x

@[simp]
theorem symm_symm : e.symm.symm = e :=
  ext $ fun x => rfl

@[simp]
theorem to_affine_equiv_symm : e.to_affine_equiv.symm = e.symm.to_affine_equiv :=
  rfl

@[simp]
theorem to_isometric_symm : e.to_isometric.symm = e.symm.to_isometric :=
  rfl

@[simp]
theorem to_homeomorph_symm : e.to_homeomorph.symm = e.symm.to_homeomorph :=
  rfl

include V₃

/--  Composition of `affine_isometry_equiv`s as a `affine_isometry_equiv`. -/
def trans (e' : P₂ ≃ᵃⁱ[𝕜] P₃) : P ≃ᵃⁱ[𝕜] P₃ :=
  ⟨e.to_affine_equiv.trans e'.to_affine_equiv, fun x => (e'.norm_map _).trans (e.norm_map _)⟩

include V V₂

@[simp]
theorem coeTransₓ (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) : ⇑e₁.trans e₂ = (e₂ ∘ e₁) :=
  rfl

omit V V₂ V₃

@[simp]
theorem trans_refl : e.trans (refl 𝕜 P₂) = e :=
  ext $ fun x => rfl

@[simp]
theorem refl_trans : (refl 𝕜 P).trans e = e :=
  ext $ fun x => rfl

@[simp]
theorem self_trans_symm : e.trans e.symm = refl 𝕜 P :=
  ext e.symm_apply_apply

@[simp]
theorem symm_trans_self : e.symm.trans e = refl 𝕜 P₂ :=
  ext e.apply_symm_apply

include V V₂ V₃

@[simp]
theorem coe_symm_trans (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) : ⇑(e₁.trans e₂).symm = (e₁.symm ∘ e₂.symm) :=
  rfl

include V₄

theorem trans_assoc (ePP₂ : P ≃ᵃⁱ[𝕜] P₂) (eP₂G : P₂ ≃ᵃⁱ[𝕜] P₃) (eGG' : P₃ ≃ᵃⁱ[𝕜] P₄) :
    ePP₂.trans (eP₂G.trans eGG') = (ePP₂.trans eP₂G).trans eGG' :=
  rfl

omit V₂ V₃ V₄

-- failed to format: format: uncaught backtrack exception
/-- The group of affine isometries of a `normed_add_torsor`, `P`. -/
  instance
    : Groupₓ ( P ≃ᵃⁱ[ 𝕜 ] P )
    where
      mul e₁ e₂ := e₂.trans e₁
        one := refl _ _
        inv := symm
        one_mul := trans_refl
        mul_one := refl_trans
        mul_assoc _ _ _ := trans_assoc _ _ _
        mul_left_inv := self_trans_symm

@[simp]
theorem coe_one : ⇑(1 : P ≃ᵃⁱ[𝕜] P) = id :=
  rfl

@[simp]
theorem coe_mul (e e' : P ≃ᵃⁱ[𝕜] P) : (⇑e*e') = (e ∘ e') :=
  rfl

@[simp]
theorem coe_inv (e : P ≃ᵃⁱ[𝕜] P) : ⇑e⁻¹ = e.symm :=
  rfl

omit V

@[simp]
theorem map_vadd (p : P) (v : V) : e (v +ᵥ p) = e.linear_isometry_equiv v +ᵥ e p :=
  e.to_affine_isometry.map_vadd p v

@[simp]
theorem map_vsub (p1 p2 : P) : e.linear_isometry_equiv (p1 -ᵥ p2) = e p1 -ᵥ e p2 :=
  e.to_affine_isometry.map_vsub p1 p2

@[simp]
theorem dist_map (x y : P) : dist (e x) (e y) = dist x y :=
  e.to_affine_isometry.dist_map x y

@[simp]
theorem edist_map (x y : P) : edist (e x) (e y) = edist x y :=
  e.to_affine_isometry.edist_map x y

protected theorem bijective : bijective e :=
  e.1.Bijective

protected theorem injective : injective e :=
  e.1.Injective

protected theorem surjective : surjective e :=
  e.1.Surjective

@[simp]
theorem map_eq_iff {x y : P} : e x = e y ↔ x = y :=
  e.injective.eq_iff

theorem map_ne {x y : P} (h : x ≠ y) : e x ≠ e y :=
  e.injective.ne h

protected theorem lipschitz : LipschitzWith 1 e :=
  e.isometry.lipschitz

protected theorem antilipschitz : AntilipschitzWith 1 e :=
  e.isometry.antilipschitz

@[simp]
theorem ediam_image (s : Set P) : Emetric.diam (e '' s) = Emetric.diam s :=
  e.isometry.ediam_image s

@[simp]
theorem diam_image (s : Set P) : Metric.diam (e '' s) = Metric.diam s :=
  e.isometry.diam_image s

variable {α : Type _} [TopologicalSpace α]

@[simp]
theorem comp_continuous_on_iff {f : α → P} {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.isometry.comp_continuous_on_iff

@[simp]
theorem comp_continuous_iff {f : α → P} : Continuous (e ∘ f) ↔ Continuous f :=
  e.isometry.comp_continuous_iff

section Constructions

variable (𝕜)

/--  The map `v ↦ v +ᵥ p` as an affine isometric equivalence between `V` and `P`. -/
def vadd_const (p : P) : V ≃ᵃⁱ[𝕜] P :=
  { AffineEquiv.vaddConst 𝕜 p with norm_map := fun x => rfl }

variable {𝕜}

include V

@[simp]
theorem coe_vadd_const (p : P) : ⇑vadd_const 𝕜 p = fun v => v +ᵥ p :=
  rfl

@[simp]
theorem coe_vadd_const_symm (p : P) : ⇑(vadd_const 𝕜 p).symm = fun p' => p' -ᵥ p :=
  rfl

@[simp]
theorem vadd_const_to_affine_equiv (p : P) : (vadd_const 𝕜 p).toAffineEquiv = AffineEquiv.vaddConst 𝕜 p :=
  rfl

omit V

variable (𝕜)

/--  `p' ↦ p -ᵥ p'` as an affine isometric equivalence. -/
def const_vsub (p : P) : P ≃ᵃⁱ[𝕜] V :=
  { AffineEquiv.constVsub 𝕜 p with norm_map := norm_neg }

variable {𝕜}

include V

@[simp]
theorem coe_const_vsub (p : P) : ⇑const_vsub 𝕜 p = (· -ᵥ ·) p :=
  rfl

@[simp]
theorem symm_const_vsub (p : P) :
    (const_vsub 𝕜 p).symm = (LinearIsometryEquiv.neg 𝕜).toAffineIsometryEquiv.trans (vadd_const 𝕜 p) := by
  ext
  rfl

omit V

variable (𝕜 P)

/--  Translation by `v` (that is, the map `p ↦ v +ᵥ p`) as an affine isometric automorphism of `P`.
-/
def const_vadd (v : V) : P ≃ᵃⁱ[𝕜] P :=
  { AffineEquiv.constVadd 𝕜 P v with norm_map := fun x => rfl }

variable {𝕜 P}

@[simp]
theorem coe_const_vadd (v : V) : ⇑(const_vadd 𝕜 P v : P ≃ᵃⁱ[𝕜] P) = (· +ᵥ ·) v :=
  rfl

@[simp]
theorem const_vadd_zero : const_vadd 𝕜 P (0 : V) = refl 𝕜 P :=
  ext $ zero_vadd V

include 𝕜 V

/--  The map `g` from `V` to `V₂` corresponding to a map `f` from `P` to `P₂`, at a base point `p`,
is an isometry if `f` is one. -/
theorem vadd_vsub {f : P → P₂} (hf : Isometry f) {p : P} {g : V → V₂} (hg : ∀ v, g v = f (v +ᵥ p) -ᵥ f p) :
    Isometry g := by
  convert (vadd_const 𝕜 (f p)).symm.Isometry.comp (hf.comp (vadd_const 𝕜 p).Isometry)
  exact funext hg

omit 𝕜

variable (𝕜)

/--  Point reflection in `x` as an affine isometric automorphism. -/
def point_reflection (x : P) : P ≃ᵃⁱ[𝕜] P :=
  (const_vsub 𝕜 x).trans (vadd_const 𝕜 x)

variable {𝕜}

theorem point_reflection_apply (x y : P) : (point_reflection 𝕜 x) y = x -ᵥ y +ᵥ x :=
  rfl

@[simp]
theorem point_reflection_to_affine_equiv (x : P) :
    (point_reflection 𝕜 x).toAffineEquiv = AffineEquiv.pointReflection 𝕜 x :=
  rfl

@[simp]
theorem point_reflection_self (x : P) : point_reflection 𝕜 x x = x :=
  AffineEquiv.point_reflection_self 𝕜 x

theorem point_reflection_involutive (x : P) : Function.Involutive (point_reflection 𝕜 x) :=
  Equivₓ.point_reflection_involutive x

@[simp]
theorem point_reflection_symm (x : P) : (point_reflection 𝕜 x).symm = point_reflection 𝕜 x :=
  to_affine_equiv_injective $ AffineEquiv.point_reflection_symm 𝕜 x

@[simp]
theorem dist_point_reflection_fixed (x y : P) : dist (point_reflection 𝕜 x y) x = dist y x := by
  rw [← (point_reflection 𝕜 x).dist_map y x, point_reflection_self]

theorem dist_point_reflection_self' (x y : P) : dist (point_reflection 𝕜 x y) y = ∥bit0 (x -ᵥ y)∥ := by
  rw [point_reflection_apply, dist_eq_norm_vsub V, vadd_vsub_assoc, bit0]

theorem dist_point_reflection_self (x y : P) : dist (point_reflection 𝕜 x y) y = ∥(2 : 𝕜)∥*dist x y := by
  rw [dist_point_reflection_self', ← two_smul' 𝕜 (x -ᵥ y), norm_smul, ← dist_eq_norm_vsub V]

theorem point_reflection_fixed_iff [Invertible (2 : 𝕜)] {x y : P} : point_reflection 𝕜 x y = y ↔ y = x :=
  AffineEquiv.point_reflection_fixed_iff_of_module 𝕜

variable [SemiNormedSpace ℝ V]

theorem dist_point_reflection_self_real (x y : P) : dist (point_reflection ℝ x y) y = 2*dist x y := by
  rw [dist_point_reflection_self, Real.norm_two]

@[simp]
theorem point_reflection_midpoint_left (x y : P) : point_reflection ℝ (midpoint ℝ x y) x = y :=
  AffineEquiv.point_reflection_midpoint_left x y

@[simp]
theorem point_reflection_midpoint_right (x y : P) : point_reflection ℝ (midpoint ℝ x y) y = x :=
  AffineEquiv.point_reflection_midpoint_right x y

end Constructions

end AffineIsometryEquiv

include V V₂

/--  If `f` is an affine map, then its linear part is continuous iff `f` is continuous. -/
theorem AffineMap.continuous_linear_iff {f : P →ᵃ[𝕜] P₂} : Continuous f.linear ↔ Continuous f := by
  inhabit P
  have :
    (f.linear : V → V₂) =
      ((AffineIsometryEquiv.vaddConst 𝕜 $ f $ default P).toHomeomorph.symm ∘
        f ∘ (AffineIsometryEquiv.vaddConst 𝕜 $ default P).toHomeomorph) :=
    by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_continuous_iff, Homeomorph.comp_continuous_iff']

/--  If `f` is an affine map, then its linear part is an open map iff `f` is an open map. -/
theorem AffineMap.is_open_map_linear_iff {f : P →ᵃ[𝕜] P₂} : IsOpenMap f.linear ↔ IsOpenMap f := by
  inhabit P
  have :
    (f.linear : V → V₂) =
      ((AffineIsometryEquiv.vaddConst 𝕜 $ f $ default P).toHomeomorph.symm ∘
        f ∘ (AffineIsometryEquiv.vaddConst 𝕜 $ default P).toHomeomorph) :=
    by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_is_open_map_iff, Homeomorph.comp_is_open_map_iff']

