import Mathbin.GroupTheory.QuotientGroup
import Mathbin.Order.Filter.Pointwise
import Mathbin.Topology.Algebra.Monoid
import Mathbin.Topology.Homeomorph
import Mathbin.Topology.Compacts

/-!
# Theory of topological groups

This file defines the following typeclasses:

* `topological_group`, `topological_add_group`: multiplicative and additive topological groups,
  i.e., groups with continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`;

* `has_continuous_sub G` means that `G` has a continuous subtraction operation.

There is an instance deducing `has_continuous_sub` from `topological_group` but we use a separate
typeclass because, e.g., `ℕ` and `ℝ≥0` have continuous subtraction but are not additive groups.

We also define `homeomorph` versions of several `equiv`s: `homeomorph.mul_left`,
`homeomorph.mul_right`, `homeomorph.inv`, and prove a few facts about neighbourhood filters in
groups.

## Tags

topological space, group, topological group
-/


open Classical Set Filter TopologicalSpace Function

open_locale Classical TopologicalSpace Filter Pointwise

universe u v w x

variable {α : Type u} {β : Type v} {G : Type w} {H : Type x}

section ContinuousMulGroup

/-!
### Groups with continuous multiplication

In this section we prove a few statements about groups with continuous `(*)`.
-/


variable [TopologicalSpace G] [Groupₓ G] [HasContinuousMul G]

/--  Multiplication from the left in a topological group as a homeomorphism. -/
@[to_additive "Addition from the left in a topological additive group as a homeomorphism."]
protected def Homeomorph.mulLeft (a : G) : G ≃ₜ G :=
  { Equivₓ.mulLeft a with continuous_to_fun := continuous_const.mul continuous_id,
    continuous_inv_fun := continuous_const.mul continuous_id }

@[simp, to_additive]
theorem Homeomorph.coe_mul_left (a : G) : ⇑Homeomorph.mulLeft a = (·*·) a :=
  rfl

@[to_additive]
theorem Homeomorph.mul_left_symm (a : G) : (Homeomorph.mulLeft a).symm = Homeomorph.mulLeft (a⁻¹) := by
  ext
  rfl

@[to_additive]
theorem is_open_map_mul_left (a : G) : IsOpenMap fun x => a*x :=
  (Homeomorph.mulLeft a).IsOpenMap

@[to_additive]
theorem is_closed_map_mul_left (a : G) : IsClosedMap fun x => a*x :=
  (Homeomorph.mulLeft a).IsClosedMap

/--  Multiplication from the right in a topological group as a homeomorphism. -/
@[to_additive "Addition from the right in a topological additive group as a homeomorphism."]
protected def Homeomorph.mulRight (a : G) : G ≃ₜ G :=
  { Equivₓ.mulRight a with continuous_to_fun := continuous_id.mul continuous_const,
    continuous_inv_fun := continuous_id.mul continuous_const }

@[simp, to_additive]
theorem Homeomorph.coe_mul_right (a : G) : ⇑Homeomorph.mulRight a = fun g => g*a :=
  rfl

@[to_additive]
theorem Homeomorph.mul_right_symm (a : G) : (Homeomorph.mulRight a).symm = Homeomorph.mulRight (a⁻¹) := by
  ext
  rfl

@[to_additive]
theorem is_open_map_mul_right (a : G) : IsOpenMap fun x => x*a :=
  (Homeomorph.mulRight a).IsOpenMap

@[to_additive]
theorem is_closed_map_mul_right (a : G) : IsClosedMap fun x => x*a :=
  (Homeomorph.mulRight a).IsClosedMap

@[to_additive]
theorem is_open_map_div_right (a : G) : IsOpenMap fun x => x / a := by
  simpa only [div_eq_mul_inv] using is_open_map_mul_right (a⁻¹)

@[to_additive]
theorem is_closed_map_div_right (a : G) : IsClosedMap fun x => x / a := by
  simpa only [div_eq_mul_inv] using is_closed_map_mul_right (a⁻¹)

@[to_additive]
theorem discrete_topology_of_open_singleton_one (h : IsOpen ({1} : Set G)) : DiscreteTopology G := by
  rw [← singletons_open_iff_discrete]
  intro g
  suffices {g} = (fun x : G => g⁻¹*x) ⁻¹' {1}by
    rw [this]
    exact (continuous_mul_left (g⁻¹)).is_open_preimage _ h
  simp only [mul_oneₓ, Set.preimage_mul_left_singleton, eq_self_iff_true, inv_invₓ, Set.singleton_eq_singleton_iff]

@[to_additive]
theorem discrete_topology_iff_open_singleton_one : DiscreteTopology G ↔ IsOpen ({1} : Set G) :=
  ⟨fun h => forall_open_iff_discrete.mpr h {1}, discrete_topology_of_open_singleton_one⟩

end ContinuousMulGroup

/-!
### Topological operations on pointwise sums and products

A few results about interior and closure of the pointwise addition/multiplication of sets in groups
with continuous addition/multiplication. See also `submonoid.top_closure_mul_self_eq` in
`topology.algebra.monoid`.
-/


section Pointwise

variable [TopologicalSpace α] [Groupₓ α] [HasContinuousMul α] {s t : Set α}

@[to_additive]
theorem IsOpen.mul_left (ht : IsOpen t) : IsOpen (s*t) := by
  rw [← Union_mul_left_image]
  exact is_open_Union fun a => is_open_Union $ fun ha => is_open_map_mul_left a t ht

@[to_additive]
theorem IsOpen.mul_right (hs : IsOpen s) : IsOpen (s*t) := by
  rw [← Union_mul_right_image]
  exact is_open_Union fun a => is_open_Union $ fun ha => is_open_map_mul_right a s hs

@[to_additive]
theorem subset_interior_mul_left : (Interior s*t) ⊆ Interior (s*t) :=
  interior_maximal (Set.mul_subset_mul_right interior_subset) is_open_interior.mul_right

@[to_additive]
theorem subset_interior_mul_right : (s*Interior t) ⊆ Interior (s*t) :=
  interior_maximal (Set.mul_subset_mul_left interior_subset) is_open_interior.mul_left

@[to_additive]
theorem subset_interior_mul : (Interior s*Interior t) ⊆ Interior (s*t) :=
  (Set.mul_subset_mul_left interior_subset).trans subset_interior_mul_left

end Pointwise

section TopologicalGroup

/-!
### Topological groups

A topological group is a group in which the multiplication and inversion operations are
continuous. Topological additive groups are defined in the same way. Equivalently, we can require
that the division operation `λ x y, x * y⁻¹` (resp., subtraction) is continuous.
-/


/--  A topological (additive) group is a group in which the addition and negation operations are
continuous. -/
class TopologicalAddGroup (G : Type u) [TopologicalSpace G] [AddGroupₓ G] extends HasContinuousAdd G : Prop where
  continuous_neg : Continuous fun a : G => -a

/--  A topological group is a group in which the multiplication and inversion operations are
continuous. -/
@[to_additive]
class TopologicalGroup (G : Type _) [TopologicalSpace G] [Groupₓ G] extends HasContinuousMul G : Prop where
  continuous_inv : Continuous (HasInv.inv : G → G)

variable [TopologicalSpace G] [Groupₓ G] [TopologicalGroup G]

export TopologicalGroup (continuous_inv)

export TopologicalAddGroup (continuous_neg)

@[to_additive]
theorem continuous_on_inv {s : Set G} : ContinuousOn HasInv.inv s :=
  continuous_inv.ContinuousOn

@[to_additive]
theorem continuous_within_at_inv {s : Set G} {x : G} : ContinuousWithinAt HasInv.inv s x :=
  continuous_inv.ContinuousWithinAt

@[to_additive]
theorem continuous_at_inv {x : G} : ContinuousAt HasInv.inv x :=
  continuous_inv.ContinuousAt

@[to_additive]
theorem tendsto_inv (a : G) : tendsto HasInv.inv (𝓝 a) (𝓝 (a⁻¹)) :=
  continuous_at_inv

/--  If a function converges to a value in a multiplicative topological group, then its inverse
converges to the inverse of this value. For the version in normed fields assuming additionally
that the limit is nonzero, use `tendsto.inv'`. -/
@[to_additive]
theorem Filter.Tendsto.inv {f : α → G} {l : Filter α} {y : G} (h : tendsto f l (𝓝 y)) :
    tendsto (fun x => f x⁻¹) l (𝓝 (y⁻¹)) :=
  (continuous_inv.Tendsto y).comp h

variable [TopologicalSpace α] {f : α → G} {s : Set α} {x : α}

@[continuity, to_additive]
theorem Continuous.inv (hf : Continuous f) : Continuous fun x => f x⁻¹ :=
  continuous_inv.comp hf

@[to_additive]
theorem ContinuousAt.inv (hf : ContinuousAt f x) : ContinuousAt (fun x => f x⁻¹) x :=
  continuous_at_inv.comp hf

@[to_additive]
theorem ContinuousOn.inv (hf : ContinuousOn f s) : ContinuousOn (fun x => f x⁻¹) s :=
  continuous_inv.comp_continuous_on hf

@[to_additive]
theorem ContinuousWithinAt.inv (hf : ContinuousWithinAt f s x) : ContinuousWithinAt (fun x => f x⁻¹) s x :=
  hf.inv

section OrderedCommGroup

variable [TopologicalSpace H] [OrderedCommGroup H] [TopologicalGroup H]

@[to_additive]
theorem tendsto_inv_nhds_within_Ioi {a : H} : tendsto HasInv.inv (𝓝[>] a) (𝓝[<] a⁻¹) :=
  (continuous_inv.Tendsto a).inf $ by
    simp [tendsto_principal_principal]

@[to_additive]
theorem tendsto_inv_nhds_within_Iio {a : H} : tendsto HasInv.inv (𝓝[<] a) (𝓝[>] a⁻¹) :=
  (continuous_inv.Tendsto a).inf $ by
    simp [tendsto_principal_principal]

@[to_additive]
theorem tendsto_inv_nhds_within_Ioi_inv {a : H} : tendsto HasInv.inv (𝓝[>] a⁻¹) (𝓝[<] a) := by
  simpa only [inv_invₓ] using @tendsto_inv_nhds_within_Ioi _ _ _ _ (a⁻¹)

@[to_additive]
theorem tendsto_inv_nhds_within_Iio_inv {a : H} : tendsto HasInv.inv (𝓝[<] a⁻¹) (𝓝[>] a) := by
  simpa only [inv_invₓ] using @tendsto_inv_nhds_within_Iio _ _ _ _ (a⁻¹)

@[to_additive]
theorem tendsto_inv_nhds_within_Ici {a : H} : tendsto HasInv.inv (𝓝[≥] a) (𝓝[≤] a⁻¹) :=
  (continuous_inv.Tendsto a).inf $ by
    simp [tendsto_principal_principal]

@[to_additive]
theorem tendsto_inv_nhds_within_Iic {a : H} : tendsto HasInv.inv (𝓝[≤] a) (𝓝[≥] a⁻¹) :=
  (continuous_inv.Tendsto a).inf $ by
    simp [tendsto_principal_principal]

@[to_additive]
theorem tendsto_inv_nhds_within_Ici_inv {a : H} : tendsto HasInv.inv (𝓝[≥] a⁻¹) (𝓝[≤] a) := by
  simpa only [inv_invₓ] using @tendsto_inv_nhds_within_Ici _ _ _ _ (a⁻¹)

@[to_additive]
theorem tendsto_inv_nhds_within_Iic_inv {a : H} : tendsto HasInv.inv (𝓝[≤] a⁻¹) (𝓝[≥] a) := by
  simpa only [inv_invₓ] using @tendsto_inv_nhds_within_Iic _ _ _ _ (a⁻¹)

end OrderedCommGroup

@[instance, to_additive]
instance [TopologicalSpace H] [Groupₓ H] [TopologicalGroup H] : TopologicalGroup (G × H) where
  continuous_inv := continuous_inv.prod_map continuous_inv

@[to_additive]
instance Pi.topological_group {C : β → Type _} [∀ b, TopologicalSpace (C b)] [∀ b, Groupₓ (C b)]
    [∀ b, TopologicalGroup (C b)] : TopologicalGroup (∀ b, C b) where
  continuous_inv := continuous_pi fun i => (continuous_apply i).inv

variable (G)

/--  Inversion in a topological group as a homeomorphism. -/
@[to_additive "Negation in a topological group as a homeomorphism."]
protected def Homeomorph.inv : G ≃ₜ G :=
  { Equivₓ.inv G with continuous_to_fun := continuous_inv, continuous_inv_fun := continuous_inv }

@[to_additive]
theorem nhds_one_symm : comap HasInv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
  ((Homeomorph.inv G).comap_nhds_eq _).trans (congr_argₓ nhds one_inv)

/--  The map `(x, y) ↦ (x, xy)` as a homeomorphism. This is a shear mapping. -/
@[to_additive "The map `(x, y) ↦ (x, x + y)` as a homeomorphism.\nThis is a shear mapping."]
protected def Homeomorph.shearMulRight : G × G ≃ₜ G × G :=
  { Equivₓ.prodShear (Equivₓ.refl _) Equivₓ.mulLeft with continuous_to_fun := continuous_fst.prod_mk continuous_mul,
    continuous_inv_fun := continuous_fst.prod_mk $ continuous_fst.inv.mul continuous_snd }

@[simp, to_additive]
theorem Homeomorph.shear_mul_right_coe : ⇑Homeomorph.shearMulRight G = fun z : G × G => (z.1, z.1*z.2) :=
  rfl

@[simp, to_additive]
theorem Homeomorph.shear_mul_right_symm_coe : ⇑(Homeomorph.shearMulRight G).symm = fun z : G × G => (z.1, z.1⁻¹*z.2) :=
  rfl

variable {G}

@[to_additive]
theorem IsOpen.inv {s : Set G} (hs : IsOpen s) : IsOpen (s⁻¹) :=
  hs.preimage continuous_inv

@[to_additive]
theorem IsClosed.inv {s : Set G} (hs : IsClosed s) : IsClosed (s⁻¹) :=
  hs.preimage continuous_inv

namespace Subgroup

@[to_additive]
instance (S : Subgroup G) : TopologicalGroup S :=
  { S.to_submonoid.has_continuous_mul with
    continuous_inv := by
      rw [embedding_subtype_coe.to_inducing.continuous_iff]
      exact continuous_subtype_coe.inv }

end Subgroup

@[to_additive]
theorem inv_closure (s : Set G) : Closure s⁻¹ = Closure (s⁻¹) :=
  (Homeomorph.inv G).preimage_closure s

/--  The (topological-space) closure of a subgroup of a space `M` with `has_continuous_mul` is
itself a subgroup. -/
@[to_additive
      "The (topological-space) closure of an additive subgroup of a space `M` with\n`has_continuous_add` is itself an additive subgroup."]
def Subgroup.topologicalClosure (s : Subgroup G) : Subgroup G :=
  { s.to_submonoid.topological_closure with Carrier := Closure (s : Set G),
    inv_mem' := fun g m => by
      simpa [← mem_inv, inv_closure] using m }

@[simp, to_additive]
theorem Subgroup.topological_closure_coe {s : Subgroup G} : (s.topological_closure : Set G) = Closure s :=
  rfl

@[to_additive]
instance Subgroup.topological_closure_topological_group (s : Subgroup G) : TopologicalGroup s.topological_closure :=
  { s.to_submonoid.topological_closure_has_continuous_mul with
    continuous_inv := by
      apply continuous_induced_rng
      change Continuous fun p : s.topological_closure => (p : G)⁻¹
      continuity }

@[to_additive]
theorem Subgroup.subgroup_topological_closure (s : Subgroup G) : s ≤ s.topological_closure :=
  subset_closure

@[to_additive]
theorem Subgroup.is_closed_topological_closure (s : Subgroup G) : IsClosed (s.topological_closure : Set G) := by
  convert is_closed_closure

@[to_additive]
theorem Subgroup.topological_closure_minimal (s : Subgroup G) {t : Subgroup G} (h : s ≤ t) (ht : IsClosed (t : Set G)) :
    s.topological_closure ≤ t :=
  closure_minimal h ht

@[to_additive]
theorem DenseRange.topological_closure_map_subgroup [Groupₓ H] [TopologicalSpace H] [TopologicalGroup H] {f : G →* H}
    (hf : Continuous f) (hf' : DenseRange f) {s : Subgroup G} (hs : s.topological_closure = ⊤) :
    (s.map f).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs⊢
  simp only [Subgroup.topological_closure_coe, Subgroup.coe_top, ← dense_iff_closure_eq] at hs⊢
  exact hf'.dense_image hf hs

@[to_additive exists_nhds_half_neg]
theorem exists_nhds_split_inv {s : Set G} (hs : s ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 (1 : G), ∀, ∀ v ∈ V, ∀, ∀ w ∈ V, ∀, v / w ∈ s :=
  have : (fun p : G × G => p.1*p.2⁻¹) ⁻¹' s ∈ 𝓝 ((1, 1) : G × G) :=
    continuous_at_fst.mul continuous_at_snd.inv
      (by
        simpa)
  by
  simpa only [div_eq_mul_inv, nhds_prod_eq, mem_prod_self_iff, prod_subset_iff, mem_preimage] using this

@[to_additive]
theorem nhds_translation_mul_inv (x : G) : comap (fun y : G => y*x⁻¹) (𝓝 1) = 𝓝 x :=
  ((Homeomorph.mulRight (x⁻¹)).comap_nhds_eq 1).trans $
    show 𝓝 (1*x⁻¹⁻¹) = 𝓝 x by
      simp

@[simp, to_additive]
theorem map_mul_left_nhds (x y : G) : map ((·*·) x) (𝓝 y) = 𝓝 (x*y) :=
  (Homeomorph.mulLeft x).map_nhds_eq y

@[to_additive]
theorem map_mul_left_nhds_one (x : G) : map ((·*·) x) (𝓝 1) = 𝓝 x := by
  simp

@[to_additive]
theorem TopologicalGroup.ext {G : Type _} [Groupₓ G] {t t' : TopologicalSpace G} (tg : @TopologicalGroup G t _)
    (tg' : @TopologicalGroup G t' _) (h : @nhds G t 1 = @nhds G t' 1) : t = t' :=
  eq_of_nhds_eq_nhds $ fun x => by
    rw [← @nhds_translation_mul_inv G t _ _ x, ← @nhds_translation_mul_inv G t' _ _ x, ← h]

@[to_additive]
theorem TopologicalGroup.of_nhds_aux {G : Type _} [Groupₓ G] [TopologicalSpace G]
    (hinv : tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1)) (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x : G => x₀*x) (𝓝 1))
    (hconj : ∀ x₀ : G, map (fun x : G => (x₀*x)*x₀⁻¹) (𝓝 1) ≤ 𝓝 1) : Continuous fun x : G => x⁻¹ := by
  rw [continuous_iff_continuous_at]
  rintro x₀
  have key : (fun x => (x₀*x)⁻¹) = ((fun x => x₀⁻¹*x) ∘ (fun x => (x₀*x)*x₀⁻¹) ∘ fun x => x⁻¹) := by
    ·
      ext <;> simp [mul_assocₓ]
  calc map (fun x => x⁻¹) (𝓝 x₀) = map (fun x => x⁻¹) ((map fun x => x₀*x) $ 𝓝 1) := by
    rw [hleft]_ = map (fun x => (x₀*x)⁻¹) (𝓝 1) := by
    rw [Filter.map_map]_ = map (((fun x => x₀⁻¹*x) ∘ fun x => (x₀*x)*x₀⁻¹) ∘ fun x => x⁻¹) (𝓝 1) := by
    rw [key]_ = map ((fun x => x₀⁻¹*x) ∘ fun x => (x₀*x)*x₀⁻¹) _ := by
    rw [← Filter.map_map]_ ≤ map ((fun x => x₀⁻¹*x) ∘ fun x => (x₀*x)*x₀⁻¹) (𝓝 1) :=
    map_mono hinv _ = map (fun x => x₀⁻¹*x) (map (fun x => (x₀*x)*x₀⁻¹) (𝓝 1)) :=
    Filter.map_map _ ≤ map (fun x => x₀⁻¹*x) (𝓝 1) := map_mono (hconj x₀)_ = 𝓝 (x₀⁻¹) := (hleft _).symm

@[to_additive]
theorem TopologicalGroup.of_nhds_one' {G : Type u} [Groupₓ G] [TopologicalSpace G]
    (hmul : tendsto (uncurry (·*· : G → G → G)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1)) (hinv : tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀*x) (𝓝 1)) (hright : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x*x₀) (𝓝 1)) :
    TopologicalGroup G := by
  refine'
    { continuous_mul := (HasContinuousMul.of_nhds_one hmul hleft hright).continuous_mul,
      continuous_inv := TopologicalGroup.of_nhds_aux hinv hleft _ }
  intro x₀
  suffices map (fun x : G => (x₀*x)*x₀⁻¹) (𝓝 1) = 𝓝 1by
    simp [this, le_reflₓ]
  rw
    [show (fun x => (x₀*x)*x₀⁻¹) = ((fun x => x₀*x) ∘ fun x => x*x₀⁻¹)by
      ext
      simp [mul_assocₓ],
    ← Filter.map_map, ← hright, hleft (x₀⁻¹), Filter.map_map]
  convert map_id
  ext
  simp

@[to_additive]
theorem TopologicalGroup.of_nhds_one {G : Type u} [Groupₓ G] [TopologicalSpace G]
    (hmul : tendsto (uncurry (·*· : G → G → G)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1)) (hinv : tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀*x) (𝓝 1))
    (hconj : ∀ x₀ : G, tendsto (fun x => (x₀*x)*x₀⁻¹) (𝓝 1) (𝓝 1)) : TopologicalGroup G :=
  { continuous_mul := by
      rw [continuous_iff_continuous_at]
      rintro ⟨x₀, y₀⟩
      have key :
        (fun p : G × G => (x₀*p.1)*y₀*p.2) =
          ((fun x => (x₀*y₀)*x) ∘ uncurry (·*·) ∘ Prod.map (fun x => (y₀⁻¹*x)*y₀) id) :=
        by
        ·
          ext
          simp [uncurry, Prod.map, mul_assocₓ]
      specialize hconj (y₀⁻¹)
      rw [inv_invₓ] at hconj
      calc map (fun p : G × G => p.1*p.2) (𝓝 (x₀, y₀)) = map (fun p : G × G => p.1*p.2) (𝓝 x₀ ×ᶠ 𝓝 y₀) := by
        rw [nhds_prod_eq]_ = map (fun p : G × G => (x₀*p.1)*y₀*p.2) (𝓝 1 ×ᶠ 𝓝 1) := by
        rw [hleft x₀, hleft y₀, prod_map_map_eq,
          Filter.map_map]_ =
          map (((fun x => (x₀*y₀)*x) ∘ uncurry (·*·)) ∘ Prod.map (fun x => (y₀⁻¹*x)*y₀) id) (𝓝 1 ×ᶠ 𝓝 1) :=
        by
        rw [key]_ = map ((fun x => (x₀*y₀)*x) ∘ uncurry (·*·)) (((map fun x => (y₀⁻¹*x)*y₀) $ 𝓝 1) ×ᶠ 𝓝 1) := by
        rw [← Filter.map_map, ← prod_map_map_eq', map_id]_ ≤ map ((fun x => (x₀*y₀)*x) ∘ uncurry (·*·)) (𝓝 1 ×ᶠ 𝓝 1) :=
        map_mono (Filter.prod_mono hconj $ le_reflₓ _)_ = map (fun x => (x₀*y₀)*x) (map (uncurry (·*·)) (𝓝 1 ×ᶠ 𝓝 1)) :=
        by
        rw [Filter.map_map]_ ≤ map (fun x => (x₀*y₀)*x) (𝓝 1) := map_mono hmul _ = 𝓝 (x₀*y₀) := (hleft _).symm,
    continuous_inv := TopologicalGroup.of_nhds_aux hinv hleft hconj }

@[to_additive]
theorem TopologicalGroup.of_comm_of_nhds_one {G : Type u} [CommGroupₓ G] [TopologicalSpace G]
    (hmul : tendsto (uncurry (·*· : G → G → G)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1)) (hinv : tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀*x) (𝓝 1)) : TopologicalGroup G :=
  TopologicalGroup.of_nhds_one hmul hinv hleft
    (by
      simpa using tendsto_id)

end TopologicalGroup

section QuotientTopologicalGroup

variable [TopologicalSpace G] [Groupₓ G] [TopologicalGroup G] (N : Subgroup G) (n : N.normal)

@[to_additive]
instance QuotientGroup.Quotient.topologicalSpace {G : Type _} [Groupₓ G] [TopologicalSpace G] (N : Subgroup G) :
    TopologicalSpace (G ⧸ N) :=
  Quotientₓ.topologicalSpace

open QuotientGroup

@[to_additive]
theorem QuotientGroup.is_open_map_coe : IsOpenMap (coeₓ : G → G ⧸ N) := by
  intro s s_op
  change IsOpen ((coeₓ : G → G ⧸ N) ⁻¹' (coeₓ '' s))
  rw [QuotientGroup.preimage_image_coe N s]
  exact is_open_Union fun n => (continuous_mul_right _).is_open_preimage s s_op

@[to_additive]
instance topological_group_quotient [N.normal] : TopologicalGroup (G ⧸ N) where
  continuous_mul := by
    have cont : Continuous ((coeₓ : G → G ⧸ N) ∘ fun p : G × G => p.fst*p.snd) := continuous_quot_mk.comp continuous_mul
    have quot : QuotientMap fun p : G × G => ((p.1 : G ⧸ N), (p.2 : G ⧸ N)) := by
      apply IsOpenMap.to_quotient_map
      ·
        exact (QuotientGroup.is_open_map_coe N).Prod (QuotientGroup.is_open_map_coe N)
      ·
        exact continuous_quot_mk.prod_map continuous_quot_mk
      ·
        exact (surjective_quot_mk _).prod_map (surjective_quot_mk _)
    exact (QuotientMap.continuous_iff Quot).2 cont
  continuous_inv := by
    have : Continuous ((coeₓ : G → G ⧸ N) ∘ fun a : G => a⁻¹) := continuous_quot_mk.comp continuous_inv
    convert continuous_quotient_lift _ this

end QuotientTopologicalGroup

/--  A typeclass saying that `λ p : G × G, p.1 - p.2` is a continuous function. This property
automatically holds for topological additive groups but it also holds, e.g., for `ℝ≥0`. -/
class HasContinuousSub (G : Type _) [TopologicalSpace G] [Sub G] : Prop where
  continuous_sub : Continuous fun p : G × G => p.1 - p.2

/--  A typeclass saying that `λ p : G × G, p.1 / p.2` is a continuous function. This property
automatically holds for topological groups. Lemmas using this class have primes.
The unprimed version is for `group_with_zero`. -/
@[to_additive]
class HasContinuousDiv (G : Type _) [TopologicalSpace G] [Div G] : Prop where
  continuous_div' : Continuous fun p : G × G => p.1 / p.2

@[to_additive]
instance (priority := 100) TopologicalGroup.to_has_continuous_div [TopologicalSpace G] [Groupₓ G] [TopologicalGroup G] :
    HasContinuousDiv G :=
  ⟨by
    simp only [div_eq_mul_inv]
    exact continuous_fst.mul continuous_snd.inv⟩

export HasContinuousSub (continuous_sub)

export HasContinuousDiv (continuous_div')

section HasContinuousDiv

variable [TopologicalSpace G] [Div G] [HasContinuousDiv G]

@[to_additive sub]
theorem Filter.Tendsto.div' {f g : α → G} {l : Filter α} {a b : G} (hf : tendsto f l (𝓝 a)) (hg : tendsto g l (𝓝 b)) :
    tendsto (fun x => f x / g x) l (𝓝 (a / b)) :=
  (continuous_div'.Tendsto (a, b)).comp (hf.prod_mk_nhds hg)

@[to_additive const_sub]
theorem Filter.Tendsto.const_div' (b : G) {c : G} {f : α → G} {l : Filter α} (h : tendsto f l (𝓝 c)) :
    tendsto (fun k : α => b / f k) l (𝓝 (b / c)) :=
  tendsto_const_nhds.div' h

@[to_additive sub_const]
theorem Filter.Tendsto.div_const' (b : G) {c : G} {f : α → G} {l : Filter α} (h : tendsto f l (𝓝 c)) :
    tendsto (fun k : α => f k / b) l (𝓝 (c / b)) :=
  h.div' tendsto_const_nhds

variable [TopologicalSpace α] {f g : α → G} {s : Set α} {x : α}

@[continuity, to_additive sub]
theorem Continuous.div' (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x / g x :=
  continuous_div'.comp (hf.prod_mk hg : _)

@[to_additive continuous_sub_left]
theorem continuous_div_left' (a : G) : Continuous fun b : G => a / b :=
  continuous_const.div' continuous_id

@[to_additive continuous_sub_right]
theorem continuous_div_right' (a : G) : Continuous fun b : G => b / a :=
  continuous_id.div' continuous_const

@[to_additive sub]
theorem ContinuousAt.div' {f g : α → G} {x : α} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => f x / g x) x :=
  hf.div' hg

@[to_additive sub]
theorem ContinuousWithinAt.div' (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => f x / g x) s x :=
  hf.div' hg

@[to_additive sub]
theorem ContinuousOn.div' (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => f x / g x) s :=
  fun x hx => (hf x hx).div' (hg x hx)

end HasContinuousDiv

@[to_additive]
theorem nhds_translation_div [TopologicalSpace G] [Groupₓ G] [TopologicalGroup G] (x : G) :
    comap (fun y : G => y / x) (𝓝 1) = 𝓝 x := by
  simpa only [div_eq_mul_inv] using nhds_translation_mul_inv x

/--  additive group with a neighbourhood around 0.
Only used to construct a topology and uniform space.

This is currently only available for commutative groups, but it can be extended to
non-commutative groups too.
-/
class AddGroupWithZeroNhd (G : Type u) extends AddCommGroupₓ G where
  z {} : Filter G
  zero_Z : pure 0 ≤ Z
  sub_Z : tendsto (fun p : G × G => p.1 - p.2) (Z ×ᶠ Z) Z

section FilterMul

section

variable (G) [TopologicalSpace G] [Groupₓ G] [TopologicalGroup G]

@[to_additive]
theorem TopologicalGroup.t1_space (h : @IsClosed G _ {1}) : T1Space G :=
  ⟨fun x => by
    convert is_closed_map_mul_right x _ h
    simp ⟩

@[to_additive]
theorem TopologicalGroup.regular_space [T1Space G] : RegularSpace G :=
  ⟨fun s a hs ha =>
    let f := fun p : G × G => p.1*p.2⁻¹
    have hf : Continuous f := continuous_fst.mul continuous_snd.inv
    let ⟨t₁, t₂, ht₁, ht₂, a_mem_t₁, one_mem_t₂, t_subset⟩ :=
      is_open_prod_iff.1 ((is_open_compl_iff.2 hs).Preimage hf) a (1 : G)
        (by
          simpa [f])
    by
    use s*t₂, ht₂.mul_left, fun x hx => ⟨x, 1, hx, one_mem_t₂, mul_oneₓ _⟩
    rw [nhdsWithin, inf_principal_eq_bot, mem_nhds_iff]
    refine' ⟨t₁, _, ht₁, a_mem_t₁⟩
    rintro x hx ⟨y, z, hy, hz, yz⟩
    have : (x*z⁻¹) ∈ sᶜ := (prod_subset_iff.1 t_subset) x hx z hz
    have : (x*z⁻¹) ∈ s
    rw [← yz]
    simpa
    contradiction⟩

attribute [local instance] TopologicalGroup.regular_space

@[to_additive]
theorem TopologicalGroup.t2_space [T1Space G] : T2Space G :=
  RegularSpace.t2_space G

end

section

/-! Some results about an open set containing the product of two sets in a topological group. -/


variable [TopologicalSpace G] [Groupₓ G] [TopologicalGroup G]

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (i «expr ∈ » t)
-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (x «expr ∈ » t)
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`\n  such that `KV ⊆ U`. -/")]
  [(Term.attributes
    "@["
    [(Term.attrInstance
      (Term.attrKind [])
      (Attr.toAdditive
       "to_additive"
       []
       [(strLit
         "\"Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of\\n`0` such that `K + V ⊆ U`.\"")]))]
    "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `compact_open_separated_mul [])
  (Command.declSig
   [(Term.implicitBinder "{" [`K `U] [":" (Term.app `Set [`G])] "}")
    (Term.explicitBinder "(" [`hK] [":" (Term.app `IsCompact [`K])] [] ")")
    (Term.explicitBinder "(" [`hU] [":" (Term.app `IsOpen [`U])] [] ")")
    (Term.explicitBinder "(" [`hKU] [":" (Init.Core.«term_⊆_» `K " ⊆ " `U)] [] ")")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `V)] [":" (Term.app `Set [`G])]))
     ","
     («term_∧_»
      (Term.app `IsOpen [`V])
      "∧"
      («term_∧_»
       (Init.Core.«term_∈_» (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" `G)]] ")") " ∈ " `V)
       "∧"
       (Init.Core.«term_⊆_» (Finset.Data.Finset.Fold.«term_*_» `K "*" `V) " ⊆ " `U))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `W
           [(Term.typeSpec ":" (Term.arrow `G "→" (Term.app `Set [`G])))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x] [])]
             "=>"
             (Set.Data.Set.Basic.«term_⁻¹'_»
              (Term.fun
               "fun"
               (Term.basicFun [(Term.simpleBinder [`y] [])] "=>" (Finset.Data.Finset.Fold.«term_*_» `x "*" `y)))
              " ⁻¹' "
              `U))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h1W []]
           [(Term.typeSpec
             ":"
             (Term.forall "∀" [(Term.simpleBinder [`x] [])] "," (Term.app `IsOpen [(Term.app `W [`x])])))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x] [])]
             "=>"
             (Term.app `hU.preimage [(Term.app `continuous_mul_left [`x])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h2W []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              []
              ","
              (Mathlib.ExtendedBinder.«term∀___,_»
               "∀"
               `x
               («binderTerm∈_» "∈" `K)
               ","
               (Term.forall
                "∀"
                []
                ","
                (Init.Core.«term_∈_»
                 (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" `G)]] ")")
                 " ∈ "
                 (Term.app `W [`x]))))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x `hx] [])]
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.simp
                   "simp"
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `mem_preimage)
                     ","
                     (Tactic.simpLemma [] [] `mul_oneₓ)
                     ","
                     (Tactic.simpLemma [] [] (Term.app `hKU [`hx]))]
                    "]"]
                   [])
                  [])]))))))))
        [])
       (group
        (Tactic.choose
         "choose"
         [`V `hV]
         ["using"
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [(Term.typeSpec ":" `K)])]
            "=>"
            (Term.app
             `exists_open_nhds_one_mul_subset
             [(Term.app
               (Term.proj (Term.app `h1W [`x]) "." `mem_nhds)
               [(Term.app `h2W [(Term.proj `x "." (fieldIdx "1")) (Term.proj `x "." (fieldIdx "2"))])])])))])
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `X
           [(Term.typeSpec ":" (Term.arrow `K "→" (Term.app `Set [`G])))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x] [])]
             "=>"
             (Set.Data.Set.Basic.«term_⁻¹'_»
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`y] [])]
                "=>"
                (Finset.Data.Finset.Fold.«term_*_»
                 (Init.Logic.«term_⁻¹» (Term.paren "(" [`x [(Term.typeAscription ":" `G)]] ")") "⁻¹")
                 "*"
                 `y)))
              " ⁻¹' "
              (Term.app `V [`x])))))))
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `t)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ht)]) [])]
             "⟩")])]
         [":"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders
             [(Lean.binderIdent `t)]
             [":" (Term.app `Finset [(Init.Coe.«term↥_» "↥" `K)])]))
           ","
           (Init.Core.«term_⊆_»
            `K
            " ⊆ "
            (Set.Data.Set.Lattice.«term⋃_,_»
             "⋃"
             (Lean.explicitBinders
              [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
               (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `i " ∈ " `t) ")")])
             ", "
             (Term.app `X [`i]))))]
         [])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.refine'
              "refine'"
              (Term.app
               `hK.elim_finite_subcover
               [`X
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`x] [])]
                  "=>"
                  (Term.app
                   (Term.proj (Term.proj (Term.app `hV [`x]) "." (fieldIdx "1")) "." `Preimage)
                   [(Term.app `continuous_mul_left [(Init.Logic.«term_⁻¹» `x "⁻¹")])])))
                (Term.hole "_")]))
             [])
            (group (Tactic.intro "intro" [`x `hx]) [])
            (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_Union)] "]") []) [])
            (group (Tactic.use "use" [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) [])
            (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_preimage)] "]") []) [])
            (group
             (Tactic.convert
              "convert"
              []
              (Term.proj (Term.proj (Term.app `hV [(Term.hole "_")]) "." (fieldIdx "2")) "." (fieldIdx "1"))
              [])
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `mul_left_invₓ) "," (Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
              [])
             [])])))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Set.Data.Set.Lattice.«term⋂_,_»
            "⋂"
            (Lean.explicitBinders
             [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
              (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
            ", "
            (Term.app `V [`x]))
           ","
           (Term.app
            `is_open_bInter
            [(Term.app `finite_mem_finset [(Term.hole "_")])
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`x `hx] [])]
               "=>"
               (Term.proj (Term.app `hV [`x]) "." (fieldIdx "1"))))])
           ","
           (Term.hole "_")
           ","
           (Term.hole "_")]
          "⟩"))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `mem_Inter)] "]"] []) [])
            (group (Tactic.intro "intro" [`x `hx]) [])
            (group
             (Tactic.exact "exact" (Term.proj (Term.proj (Term.app `hV [`x]) "." (fieldIdx "2")) "." (fieldIdx "1")))
             [])])))
        [])
       (group
        (Tactic.rintro
         "rintro"
         [(Tactic.rintroPat.one (Tactic.rcasesPat.ignore "_"))
          (Tactic.rintroPat.one
           (Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hy)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
            "⟩"))]
         [])
        [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `mem_Inter)] "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
        [])
       (group (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `ht [`hx])))) [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `mem_Union) "," (Tactic.simpLemma [] [] `mem_preimage)] "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
        [])
       (group
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `this)]
         ["with"
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `z)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h1z)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h2z)]) [])]
           "⟩")])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Init.Core.«term_∈_»
              (Finset.Data.Finset.Fold.«term_*_»
               (Finset.Data.Finset.Fold.«term_*_»
                (Init.Logic.«term_⁻¹» (Term.paren "(" [`z [(Term.typeAscription ":" `G)]] ")") "⁻¹")
                "*"
                `x)
               "*"
               `y)
              " ∈ "
              (Term.app `W [`z])))]
           ":="
           (Term.app
            (Term.proj (Term.proj (Term.app `hV [`z]) "." (fieldIdx "2")) "." (fieldIdx "2"))
            [(Term.app `mul_mem_mul [`h2z (Term.app `hy [`z `h1z])])]))))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_preimage)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
        [])
       (group (Tactic.convert "convert" [] `this ["using" (numLit "1")]) [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `mul_assocₓ) "," (Tactic.simpLemma [] [] `mul_inv_cancel_left)] "]"]
         [])
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `W
          [(Term.typeSpec ":" (Term.arrow `G "→" (Term.app `Set [`G])))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [])]
            "=>"
            (Set.Data.Set.Basic.«term_⁻¹'_»
             (Term.fun
              "fun"
              (Term.basicFun [(Term.simpleBinder [`y] [])] "=>" (Finset.Data.Finset.Fold.«term_*_» `x "*" `y)))
             " ⁻¹' "
             `U))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h1W []]
          [(Term.typeSpec
            ":"
            (Term.forall "∀" [(Term.simpleBinder [`x] [])] "," (Term.app `IsOpen [(Term.app `W [`x])])))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [])]
            "=>"
            (Term.app `hU.preimage [(Term.app `continuous_mul_left [`x])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h2W []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             []
             ","
             (Mathlib.ExtendedBinder.«term∀___,_»
              "∀"
              `x
              («binderTerm∈_» "∈" `K)
              ","
              (Term.forall
               "∀"
               []
               ","
               (Init.Core.«term_∈_»
                (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" `G)]] ")")
                " ∈ "
                (Term.app `W [`x]))))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x `hx] [])]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `mem_preimage)
                    ","
                    (Tactic.simpLemma [] [] `mul_oneₓ)
                    ","
                    (Tactic.simpLemma [] [] (Term.app `hKU [`hx]))]
                   "]"]
                  [])
                 [])]))))))))
       [])
      (group
       (Tactic.choose
        "choose"
        [`V `hV]
        ["using"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x] [(Term.typeSpec ":" `K)])]
           "=>"
           (Term.app
            `exists_open_nhds_one_mul_subset
            [(Term.app
              (Term.proj (Term.app `h1W [`x]) "." `mem_nhds)
              [(Term.app `h2W [(Term.proj `x "." (fieldIdx "1")) (Term.proj `x "." (fieldIdx "2"))])])])))])
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `X
          [(Term.typeSpec ":" (Term.arrow `K "→" (Term.app `Set [`G])))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [])]
            "=>"
            (Set.Data.Set.Basic.«term_⁻¹'_»
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`y] [])]
               "=>"
               (Finset.Data.Finset.Fold.«term_*_»
                (Init.Logic.«term_⁻¹» (Term.paren "(" [`x [(Term.typeAscription ":" `G)]] ")") "⁻¹")
                "*"
                `y)))
             " ⁻¹' "
             (Term.app `V [`x])))))))
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `t)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ht)]) [])]
            "⟩")])]
        [":"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders
           (Lean.unbracketedExplicitBinders
            [(Lean.binderIdent `t)]
            [":" (Term.app `Finset [(Init.Coe.«term↥_» "↥" `K)])]))
          ","
          (Init.Core.«term_⊆_»
           `K
           " ⊆ "
           (Set.Data.Set.Lattice.«term⋃_,_»
            "⋃"
            (Lean.explicitBinders
             [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
              (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `i " ∈ " `t) ")")])
            ", "
            (Term.app `X [`i]))))]
        [])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.refine'
             "refine'"
             (Term.app
              `hK.elim_finite_subcover
              [`X
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`x] [])]
                 "=>"
                 (Term.app
                  (Term.proj (Term.proj (Term.app `hV [`x]) "." (fieldIdx "1")) "." `Preimage)
                  [(Term.app `continuous_mul_left [(Init.Logic.«term_⁻¹» `x "⁻¹")])])))
               (Term.hole "_")]))
            [])
           (group (Tactic.intro "intro" [`x `hx]) [])
           (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_Union)] "]") []) [])
           (group (Tactic.use "use" [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) [])
           (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_preimage)] "]") []) [])
           (group
            (Tactic.convert
             "convert"
             []
             (Term.proj (Term.proj (Term.app `hV [(Term.hole "_")]) "." (fieldIdx "2")) "." (fieldIdx "1"))
             [])
            [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `mul_left_invₓ) "," (Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(Set.Data.Set.Lattice.«term⋂_,_»
           "⋂"
           (Lean.explicitBinders
            [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
             (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
           ", "
           (Term.app `V [`x]))
          ","
          (Term.app
           `is_open_bInter
           [(Term.app `finite_mem_finset [(Term.hole "_")])
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`x `hx] [])]
              "=>"
              (Term.proj (Term.app `hV [`x]) "." (fieldIdx "1"))))])
          ","
          (Term.hole "_")
          ","
          (Term.hole "_")]
         "⟩"))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `mem_Inter)] "]"] []) [])
           (group (Tactic.intro "intro" [`x `hx]) [])
           (group
            (Tactic.exact "exact" (Term.proj (Term.proj (Term.app `hV [`x]) "." (fieldIdx "2")) "." (fieldIdx "1")))
            [])])))
       [])
      (group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one (Tactic.rcasesPat.ignore "_"))
         (Tactic.rintroPat.one
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hy)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
           "⟩"))]
        [])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `mem_Inter)] "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
       [])
      (group (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `ht [`hx])))) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `mem_Union) "," (Tactic.simpLemma [] [] `mem_preimage)] "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] `this)]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `z)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h1z)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h2z)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Init.Core.«term_∈_»
             (Finset.Data.Finset.Fold.«term_*_»
              (Finset.Data.Finset.Fold.«term_*_»
               (Init.Logic.«term_⁻¹» (Term.paren "(" [`z [(Term.typeAscription ":" `G)]] ")") "⁻¹")
               "*"
               `x)
              "*"
              `y)
             " ∈ "
             (Term.app `W [`z])))]
          ":="
          (Term.app
           (Term.proj (Term.proj (Term.app `hV [`z]) "." (fieldIdx "2")) "." (fieldIdx "2"))
           [(Term.app `mul_mem_mul [`h2z (Term.app `hy [`z `h1z])])]))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_preimage)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
       [])
      (group (Tactic.convert "convert" [] `this ["using" (numLit "1")]) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `mul_assocₓ) "," (Tactic.simpLemma [] [] `mul_inv_cancel_left)] "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `mul_assocₓ) "," (Tactic.simpLemma [] [] `mul_inv_cancel_left)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_inv_cancel_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_assocₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.convert "convert" [] `this ["using" (numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.convert', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_preimage)] "]")
   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_preimage
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       (Init.Core.«term_∈_»
        (Finset.Data.Finset.Fold.«term_*_»
         (Finset.Data.Finset.Fold.«term_*_»
          (Init.Logic.«term_⁻¹» (Term.paren "(" [`z [(Term.typeAscription ":" `G)]] ")") "⁻¹")
          "*"
          `x)
         "*"
         `y)
        " ∈ "
        (Term.app `W [`z])))]
     ":="
     (Term.app
      (Term.proj (Term.proj (Term.app `hV [`z]) "." (fieldIdx "2")) "." (fieldIdx "2"))
      [(Term.app `mul_mem_mul [`h2z (Term.app `hy [`z `h1z])])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.proj (Term.app `hV [`z]) "." (fieldIdx "2")) "." (fieldIdx "2"))
   [(Term.app `mul_mem_mul [`h2z (Term.app `hy [`z `h1z])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_mem_mul [`h2z (Term.app `hy [`z `h1z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hy [`z `h1z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h1z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hy
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hy [`z `h1z]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `h2z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_mem_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `mul_mem_mul [`h2z (Term.paren "(" [(Term.app `hy [`z `h1z]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.proj (Term.app `hV [`z]) "." (fieldIdx "2")) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `hV [`z]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hV [`z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hV
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hV [`z]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Finset.Data.Finset.Fold.«term_*_»
     (Init.Logic.«term_⁻¹» (Term.paren "(" [`z [(Term.typeAscription ":" `G)]] ")") "⁻¹")
     "*"
     `x)
    "*"
    `y)
   " ∈ "
   (Term.app `W [`z]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `W [`z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `W
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Init.Logic.«term_⁻¹» (Term.paren "(" [`z [(Term.typeAscription ":" `G)]] ")") "⁻¹")
    "*"
    `x)
   "*"
   `y)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Init.Logic.«term_⁻¹» (Term.paren "(" [`z [(Term.typeAscription ":" `G)]] ")") "⁻¹")
   "*"
   `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Init.Logic.«term_⁻¹» (Term.paren "(" [`z [(Term.typeAscription ":" `G)]] ")") "⁻¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_⁻¹»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.paren "(" [`z [(Term.typeAscription ":" `G)]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `G
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Init.Logic.«term_⁻¹» (Term.paren "(" [`z [(Term.typeAscription ":" `G)]] ")") "⁻¹")
   "*"
   `x)
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Term.paren
    "("
    [(Finset.Data.Finset.Fold.«term_*_»
      (Init.Logic.«term_⁻¹» (Term.paren "(" [`z [(Term.typeAscription ":" `G)]] ")") "⁻¹")
      "*"
      `x)
     []]
    ")")
   "*"
   `y)
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] `this)]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `z)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h1z)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h2z)]) [])]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `mem_Union) "," (Tactic.simpLemma [] [] `mem_preimage)] "]"]
   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_preimage
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `ht [`hx]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ht [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ht
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `mem_Inter)] "]"]
   [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hy
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_Inter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rintro
   "rintro"
   [(Tactic.rintroPat.one (Tactic.rcasesPat.ignore "_"))
    (Tactic.rintroPat.one
     (Tactic.rcasesPat.tuple
      "⟨"
      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hy)]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
      "⟩"))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.ignore', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `mem_Inter)] "]"] []) [])
      (group (Tactic.intro "intro" [`x `hx]) [])
      (group
       (Tactic.exact "exact" (Term.proj (Term.proj (Term.app `hV [`x]) "." (fieldIdx "2")) "." (fieldIdx "1")))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.proj (Term.proj (Term.app `hV [`x]) "." (fieldIdx "2")) "." (fieldIdx "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.proj (Term.app `hV [`x]) "." (fieldIdx "2")) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `hV [`x]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hV [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hV
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hV [`x]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`x `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `mem_Inter)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_Inter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.anonymousCtor
    "⟨"
    [(Set.Data.Set.Lattice.«term⋂_,_»
      "⋂"
      (Lean.explicitBinders
       [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
        (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
      ", "
      (Term.app `V [`x]))
     ","
     (Term.app
      `is_open_bInter
      [(Term.app `finite_mem_finset [(Term.hole "_")])
       (Term.fun
        "fun"
        (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.proj (Term.app `hV [`x]) "." (fieldIdx "1"))))])
     ","
     (Term.hole "_")
     ","
     (Term.hole "_")]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Set.Data.Set.Lattice.«term⋂_,_»
     "⋂"
     (Lean.explicitBinders
      [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
       (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
     ", "
     (Term.app `V [`x]))
    ","
    (Term.app
     `is_open_bInter
     [(Term.app `finite_mem_finset [(Term.hole "_")])
      (Term.fun
       "fun"
       (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.proj (Term.app `hV [`x]) "." (fieldIdx "1"))))])
    ","
    (Term.hole "_")
    ","
    (Term.hole "_")]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `is_open_bInter
   [(Term.app `finite_mem_finset [(Term.hole "_")])
    (Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.proj (Term.app `hV [`x]) "." (fieldIdx "1"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.proj (Term.app `hV [`x]) "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `hV [`x]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hV [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hV
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hV [`x]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app `finite_mem_finset [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `finite_mem_finset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `finite_mem_finset [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `is_open_bInter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋂_,_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋂_,_»
   "⋂"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
   ", "
   (Term.app `V [`x]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋂_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `V [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `V
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
        such that `KV ⊆ U`. -/
    @[
      to_additive
        "Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of\n`0` such that `K + V ⊆ U`."
      ]
  theorem
    compact_open_separated_mul
    { K U : Set G } ( hK : IsCompact K ) ( hU : IsOpen U ) ( hKU : K ⊆ U )
      : ∃ V : Set G , IsOpen V ∧ ( 1 : G ) ∈ V ∧ K * V ⊆ U
    :=
      by
        let W : G → Set G := fun x => fun y => x * y ⁻¹' U
          have h1W : ∀ x , IsOpen W x := fun x => hU.preimage continuous_mul_left x
          have h2W : ∀ , ∀ x ∈ K , ∀ , ( 1 : G ) ∈ W x := fun x hx => by simp only [ mem_preimage , mul_oneₓ , hKU hx ]
          choose V hV using fun x : K => exists_open_nhds_one_mul_subset h1W x . mem_nhds h2W x . 1 x . 2
          let X : K → Set G := fun x => fun y => ( x : G ) ⁻¹ * y ⁻¹' V x
          obtain ⟨ t , ht ⟩ : ∃ t : Finset ↥ K , K ⊆ ⋃ ( i : _ ) ( _ : i ∈ t ) , X i
          ·
            refine' hK.elim_finite_subcover X fun x => hV x . 1 . Preimage continuous_mul_left x ⁻¹ _
              intro x hx
              rw [ mem_Union ]
              use ⟨ x , hx ⟩
              rw [ mem_preimage ]
              convert hV _ . 2 . 1
              simp only [ mul_left_invₓ , Subtype.coe_mk ]
          refine' ⟨ ⋂ ( x : _ ) ( _ : x ∈ t ) , V x , is_open_bInter finite_mem_finset _ fun x hx => hV x . 1 , _ , _ ⟩
          · simp only [ mem_Inter ] intro x hx exact hV x . 2 . 1
          rintro _ ⟨ x , y , hx , hy , rfl ⟩
          simp only [ mem_Inter ] at hy
          have := ht hx
          simp only [ mem_Union , mem_preimage ] at this
          rcases this with ⟨ z , h1z , h2z ⟩
          have : ( z : G ) ⁻¹ * x * y ∈ W z := hV z . 2 . 2 mul_mem_mul h2z hy z h1z
          rw [ mem_preimage ] at this
          convert this using 1
          simp only [ mul_assocₓ , mul_inv_cancel_left ]

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (x «expr ∈ » t)
-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (g «expr ∈ » t)
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " A compact set is covered by finitely many left multiplicative translates of a set\n  with non-empty interior. -/")]
  [(Term.attributes
    "@["
    [(Term.attrInstance
      (Term.attrKind [])
      (Attr.toAdditive
       "to_additive"
       []
       [(strLit
         "\"A compact set is covered by finitely many left additive translates of a set\\n  with non-empty interior.\"")]))]
    "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `compact_covered_by_mul_left_translates [])
  (Command.declSig
   [(Term.implicitBinder "{" [`K `V] [":" (Term.app `Set [`G])] "}")
    (Term.explicitBinder "(" [`hK] [":" (Term.app `IsCompact [`K])] [] ")")
    (Term.explicitBinder "(" [`hV] [":" (Term.proj (Term.app `Interior [`V]) "." `Nonempty)] [] ")")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `t)] [":" (Term.app `Finset [`G])]))
     ","
     (Init.Core.«term_⊆_»
      `K
      " ⊆ "
      (Set.Data.Set.Lattice.«term⋃_,_»
       "⋃"
       (Lean.explicitBinders
        [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `g)] ":" (Term.hole "_") ")")
         (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `g " ∈ " `t) ")")])
       ", "
       (Set.Data.Set.Basic.«term_⁻¹'_»
        (Term.fun
         "fun"
         (Term.basicFun [(Term.simpleBinder [`h] [])] "=>" (Finset.Data.Finset.Fold.«term_*_» `g "*" `h)))
        " ⁻¹' "
        `V))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `t)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ht)]) [])]
             "⟩")])]
         [":"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders [(Lean.binderIdent `t)] [":" (Term.app `Finset [`G])]))
           ","
           (Init.Core.«term_⊆_»
            `K
            " ⊆ "
            (Set.Data.Set.Lattice.«term⋃_,_»
             "⋃"
             (Lean.explicitBinders
              [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
               (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
             ", "
             (Term.app
              `Interior
              [(Set.Data.Set.Basic.«term_⁻¹'_»
                (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
                " ⁻¹' "
                `V)]))))]
         [])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.refine'
              "refine'"
              (Term.app
               `hK.elim_finite_subcover
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`x] [])]
                  "=>"
                  («term_$__»
                   `Interior
                   "$"
                   (Set.Data.Set.Basic.«term_⁻¹'_»
                    (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
                    " ⁻¹' "
                    `V))))
                (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" `is_open_interior))
                (Term.hole "_")]))
             [])
            (group
             (Tactic.cases'
              "cases'"
              [(Tactic.casesTarget [] `hV)]
              []
              ["with" [(Lean.binderIdent `g₀) (Lean.binderIdent `hg₀)]])
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`g `hg] [])]
                "=>"
                (Term.app
                 (Term.proj `mem_Union "." (fieldIdx "2"))
                 [(Term.anonymousCtor
                   "⟨"
                   [(Finset.Data.Finset.Fold.«term_*_» `g₀ "*" (Init.Logic.«term_⁻¹» `g "⁻¹")) "," (Term.hole "_")]
                   "⟩")]))))
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.app
               `preimage_interior_subset_interior_preimage
               [(Term.app `continuous_const.mul [`continuous_id]) (Term.hole "_")]))
             [])
            (group
             (tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_preimage) "," (Tactic.rwRule [] `inv_mul_cancel_right)] "]")
              [])
             [])])))
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [`t
           ","
           («term_$__»
            (Term.app `subset.trans [`ht])
            "$"
            («term_$__»
             `bUnion_mono
             "$"
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`g `hg] [])] "=>" `interior_subset))))]
          "⟩"))
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `t)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ht)]) [])]
            "⟩")])]
        [":"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `t)] [":" (Term.app `Finset [`G])]))
          ","
          (Init.Core.«term_⊆_»
           `K
           " ⊆ "
           (Set.Data.Set.Lattice.«term⋃_,_»
            "⋃"
            (Lean.explicitBinders
             [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
              (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
            ", "
            (Term.app
             `Interior
             [(Set.Data.Set.Basic.«term_⁻¹'_»
               (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
               " ⁻¹' "
               `V)]))))]
        [])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.refine'
             "refine'"
             (Term.app
              `hK.elim_finite_subcover
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`x] [])]
                 "=>"
                 («term_$__»
                  `Interior
                  "$"
                  (Set.Data.Set.Basic.«term_⁻¹'_»
                   (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
                   " ⁻¹' "
                   `V))))
               (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" `is_open_interior))
               (Term.hole "_")]))
            [])
           (group
            (Tactic.cases'
             "cases'"
             [(Tactic.casesTarget [] `hV)]
             []
             ["with" [(Lean.binderIdent `g₀) (Lean.binderIdent `hg₀)]])
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`g `hg] [])]
               "=>"
               (Term.app
                (Term.proj `mem_Union "." (fieldIdx "2"))
                [(Term.anonymousCtor
                  "⟨"
                  [(Finset.Data.Finset.Fold.«term_*_» `g₀ "*" (Init.Logic.«term_⁻¹» `g "⁻¹")) "," (Term.hole "_")]
                  "⟩")]))))
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              `preimage_interior_subset_interior_preimage
              [(Term.app `continuous_const.mul [`continuous_id]) (Term.hole "_")]))
            [])
           (group
            (tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_preimage) "," (Tactic.rwRule [] `inv_mul_cancel_right)] "]")
             [])
            [])])))
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.anonymousCtor
         "⟨"
         [`t
          ","
          («term_$__»
           (Term.app `subset.trans [`ht])
           "$"
           («term_$__»
            `bUnion_mono
            "$"
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`g `hg] [])] "=>" `interior_subset))))]
         "⟩"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.anonymousCtor
    "⟨"
    [`t
     ","
     («term_$__»
      (Term.app `subset.trans [`ht])
      "$"
      («term_$__»
       `bUnion_mono
       "$"
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`g `hg] [])] "=>" `interior_subset))))]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`t
    ","
    («term_$__»
     (Term.app `subset.trans [`ht])
     "$"
     («term_$__»
      `bUnion_mono
      "$"
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`g `hg] [])] "=>" `interior_subset))))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.app `subset.trans [`ht])
   "$"
   («term_$__»
    `bUnion_mono
    "$"
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`g `hg] [])] "=>" `interior_subset))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__» `bUnion_mono "$" (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`g `hg] [])] "=>" `interior_subset)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`g `hg] [])] "=>" `interior_subset))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `interior_subset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `bUnion_mono
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.app `subset.trans [`ht])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ht
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `subset.trans
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.refine'
        "refine'"
        (Term.app
         `hK.elim_finite_subcover
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [])]
            "=>"
            («term_$__»
             `Interior
             "$"
             (Set.Data.Set.Basic.«term_⁻¹'_»
              (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
              " ⁻¹' "
              `V))))
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" `is_open_interior))
          (Term.hole "_")]))
       [])
      (group
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget [] `hV)]
        []
        ["with" [(Lean.binderIdent `g₀) (Lean.binderIdent `hg₀)]])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`g `hg] [])]
          "=>"
          (Term.app
           (Term.proj `mem_Union "." (fieldIdx "2"))
           [(Term.anonymousCtor
             "⟨"
             [(Finset.Data.Finset.Fold.«term_*_» `g₀ "*" (Init.Logic.«term_⁻¹» `g "⁻¹")) "," (Term.hole "_")]
             "⟩")]))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `preimage_interior_subset_interior_preimage
         [(Term.app `continuous_const.mul [`continuous_id]) (Term.hole "_")]))
       [])
      (group
       (tacticRwa__
        "rwa"
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_preimage) "," (Tactic.rwRule [] `inv_mul_cancel_right)] "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticRwa__
   "rwa"
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_preimage) "," (Tactic.rwRule [] `inv_mul_cancel_right)] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticRwa__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `inv_mul_cancel_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_preimage
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `preimage_interior_subset_interior_preimage
    [(Term.app `continuous_const.mul [`continuous_id]) (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `preimage_interior_subset_interior_preimage
   [(Term.app `continuous_const.mul [`continuous_id]) (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app `continuous_const.mul [`continuous_id])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `continuous_id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `continuous_const.mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `continuous_const.mul [`continuous_id]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `preimage_interior_subset_interior_preimage
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`g `hg] [])]
     "=>"
     (Term.app
      (Term.proj `mem_Union "." (fieldIdx "2"))
      [(Term.anonymousCtor
        "⟨"
        [(Finset.Data.Finset.Fold.«term_*_» `g₀ "*" (Init.Logic.«term_⁻¹» `g "⁻¹")) "," (Term.hole "_")]
        "⟩")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`g `hg] [])]
    "=>"
    (Term.app
     (Term.proj `mem_Union "." (fieldIdx "2"))
     [(Term.anonymousCtor
       "⟨"
       [(Finset.Data.Finset.Fold.«term_*_» `g₀ "*" (Init.Logic.«term_⁻¹» `g "⁻¹")) "," (Term.hole "_")]
       "⟩")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `mem_Union "." (fieldIdx "2"))
   [(Term.anonymousCtor
     "⟨"
     [(Finset.Data.Finset.Fold.«term_*_» `g₀ "*" (Init.Logic.«term_⁻¹» `g "⁻¹")) "," (Term.hole "_")]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Finset.Data.Finset.Fold.«term_*_» `g₀ "*" (Init.Logic.«term_⁻¹» `g "⁻¹")) "," (Term.hole "_")]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `g₀ "*" (Init.Logic.«term_⁻¹» `g "⁻¹"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_⁻¹» `g "⁻¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_⁻¹»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g₀
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `mem_Union "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `mem_Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.cases' "cases'" [(Tactic.casesTarget [] `hV)] [] ["with" [(Lean.binderIdent `g₀) (Lean.binderIdent `hg₀)]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases'', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hV
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `hK.elim_finite_subcover
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`x] [])]
       "=>"
       («term_$__»
        `Interior
        "$"
        (Set.Data.Set.Basic.«term_⁻¹'_»
         (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
         " ⁻¹' "
         `V))))
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" `is_open_interior))
     (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `hK.elim_finite_subcover
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x] [])]
      "=>"
      («term_$__»
       `Interior
       "$"
       (Set.Data.Set.Basic.«term_⁻¹'_»
        (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
        " ⁻¹' "
        `V))))
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" `is_open_interior))
    (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" `is_open_interior))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `is_open_interior
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" `is_open_interior)) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [])]
    "=>"
    («term_$__»
     `Interior
     "$"
     (Set.Data.Set.Basic.«term_⁻¹'_»
      (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
      " ⁻¹' "
      `V))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   `Interior
   "$"
   (Set.Data.Set.Basic.«term_⁻¹'_»
    (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
    " ⁻¹' "
    `V))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Basic.«term_⁻¹'_»
   (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
   " ⁻¹' "
   `V)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `V
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.cdot "·")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'Lean.Parser.Term.cdot.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.cdot "·")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'Lean.Parser.Term.cdot.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `Interior
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [])]
    "=>"
    («term_$__»
     `Interior
     "$"
     (Set.Data.Set.Basic.«term_⁻¹'_»
      (Term.app (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) []] ")") [`x])
      " ⁻¹' "
      `V))))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hK.elim_finite_subcover
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.obtain
   "obtain"
   [(Tactic.rcasesPatMed
     [(Tactic.rcasesPat.tuple
       "⟨"
       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `t)]) [])
        ","
        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ht)]) [])]
       "⟩")])]
   [":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `t)] [":" (Term.app `Finset [`G])]))
     ","
     (Init.Core.«term_⊆_»
      `K
      " ⊆ "
      (Set.Data.Set.Lattice.«term⋃_,_»
       "⋃"
       (Lean.explicitBinders
        [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
         (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
       ", "
       (Term.app
        `Interior
        [(Set.Data.Set.Basic.«term_⁻¹'_»
          (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
          " ⁻¹' "
          `V)]))))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.obtain', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term∃_,_»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term∃_,_»
   "∃"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `t)] [":" (Term.app `Finset [`G])]))
   ","
   (Init.Core.«term_⊆_»
    `K
    " ⊆ "
    (Set.Data.Set.Lattice.«term⋃_,_»
     "⋃"
     (Lean.explicitBinders
      [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
       (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
     ", "
     (Term.app
      `Interior
      [(Set.Data.Set.Basic.«term_⁻¹'_»
        (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
        " ⁻¹' "
        `V)]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term∃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_⊆_»
   `K
   " ⊆ "
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
    ", "
    (Term.app
     `Interior
     [(Set.Data.Set.Basic.«term_⁻¹'_»
       (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
       " ⁻¹' "
       `V)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_⊆_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `x " ∈ " `t) ")")])
   ", "
   (Term.app
    `Interior
    [(Set.Data.Set.Basic.«term_⁻¹'_»
      (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
      " ⁻¹' "
      `V)]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Interior
   [(Set.Data.Set.Basic.«term_⁻¹'_»
     (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
     " ⁻¹' "
     `V)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Basic.«term_⁻¹'_»
   (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
   " ⁻¹' "
   `V)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `V
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Term.app (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.cdot "·")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'Lean.Parser.Term.cdot.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.cdot "·")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'Lean.Parser.Term.cdot.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Set.Data.Set.Basic.«term_⁻¹'_»
   (Term.app (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» (Term.cdot "·") "*" (Term.cdot "·")) []] ")") [`x])
   " ⁻¹' "
   `V)
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Interior
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      A compact set is covered by finitely many left multiplicative translates of a set
        with non-empty interior. -/
    @[
      to_additive
        "A compact set is covered by finitely many left additive translates of a set\n  with non-empty interior."
      ]
  theorem
    compact_covered_by_mul_left_translates
    { K V : Set G } ( hK : IsCompact K ) ( hV : Interior V . Nonempty )
      : ∃ t : Finset G , K ⊆ ⋃ ( g : _ ) ( _ : g ∈ t ) , fun h => g * h ⁻¹' V
    :=
      by
        obtain ⟨ t , ht ⟩ : ∃ t : Finset G , K ⊆ ⋃ ( x : _ ) ( _ : x ∈ t ) , Interior · * · x ⁻¹' V
          ·
            refine' hK.elim_finite_subcover fun x => Interior $ · * · x ⁻¹' V fun x => is_open_interior _
              cases' hV with g₀ hg₀
              refine' fun g hg => mem_Union . 2 ⟨ g₀ * g ⁻¹ , _ ⟩
              refine' preimage_interior_subset_interior_preimage continuous_const.mul continuous_id _
              rwa [ mem_preimage , inv_mul_cancel_right ]
          exact ⟨ t , subset.trans ht $ bUnion_mono $ fun g hg => interior_subset ⟩

/--  Every locally compact separable topological group is σ-compact.
  Note: this is not true if we drop the topological group hypothesis. -/
@[to_additive SeparableLocallyCompactAddGroup.sigma_compact_space]
instance (priority := 100) SeparableLocallyCompactGroup.sigma_compact_space [separable_space G]
    [LocallyCompactSpace G] : SigmaCompactSpace G := by
  obtain ⟨L, hLc, hL1⟩ := exists_compact_mem_nhds (1 : G)
  refine' ⟨⟨fun n => (fun x => x*dense_seq G n) ⁻¹' L, _, _⟩⟩
  ·
    intro n
    exact (Homeomorph.mulRight _).compact_preimage.mpr hLc
  ·
    refine' Union_eq_univ_iff.2 fun x => _
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ : (range (dense_seq G) ∩ (fun y => x*y) ⁻¹' L).Nonempty
    ·
      rw [← (Homeomorph.mulLeft x).apply_symm_apply 1] at hL1
      exact (dense_range_dense_seq G).inter_nhds_nonempty ((Homeomorph.mulLeft x).Continuous.ContinuousAt $ hL1)
    exact ⟨n, hn⟩

/--  Every separated topological group in which there exists a compact set with nonempty interior
is locally compact. -/
@[to_additive]
theorem TopologicalSpace.PositiveCompacts.locally_compact_space_of_group [T2Space G] (K : positive_compacts G) :
    LocallyCompactSpace G := by
  refine' locally_compact_of_compact_nhds fun x => _
  obtain ⟨y, hy⟩ : ∃ y, y ∈ Interior K.1 := K.2.2
  let F := Homeomorph.mulLeft (x*y⁻¹)
  refine' ⟨F '' K.1, _, IsCompact.image K.2.1 F.continuous⟩
  suffices F.symm ⁻¹' K.1 ∈ 𝓝 x by
    ·
      convert this
      apply Equivₓ.image_eq_preimage
  apply ContinuousAt.preimage_mem_nhds F.symm.continuous.continuous_at
  have : F.symm x = y := by
    simp [F, Homeomorph.mul_left_symm]
  rw [this]
  exact mem_interior_iff_mem_nhds.1 hy

end

section

variable [TopologicalSpace G] [CommGroupₓ G] [TopologicalGroup G]

@[to_additive]
theorem nhds_mul (x y : G) : 𝓝 (x*y) = 𝓝 x*𝓝 y :=
  filter_eq $
    Set.ext $ fun s => by
      rw [← nhds_translation_mul_inv x, ← nhds_translation_mul_inv y, ← nhds_translation_mul_inv (x*y)]
      constructor
      ·
        rintro ⟨t, ht, ts⟩
        rcases exists_nhds_one_split ht with ⟨V, V1, h⟩
        refine' ⟨(fun a => a*x⁻¹) ⁻¹' V, (fun a => a*y⁻¹) ⁻¹' V, ⟨V, V1, subset.refl _⟩, ⟨V, V1, subset.refl _⟩, _⟩
        rintro a ⟨v, w, v_mem, w_mem, rfl⟩
        apply ts
        simpa [mul_commₓ, mul_assocₓ, mul_left_commₓ] using h (v*x⁻¹) v_mem (w*y⁻¹) w_mem
      ·
        rintro ⟨a, c, ⟨b, hb, ba⟩, ⟨d, hd, dc⟩, ac⟩
        refine' ⟨b ∩ d, inter_mem hb hd, fun v => _⟩
        simp only [preimage_subset_iff, mul_inv_rev, mem_preimage] at *
        rintro ⟨vb, vd⟩
        refine' ac ⟨v*y⁻¹, y, _, _, _⟩
        ·
          rw [← mul_assocₓ _ _ _] at vb
          exact ba _ vb
        ·
          apply dc y
          rw [mul_right_invₓ]
          exact mem_of_mem_nhds hd
        ·
          simp only [inv_mul_cancel_right]

/--  On a topological group, `𝓝 : G → filter G` can be promoted to a `mul_hom`. -/
@[to_additive "On an additive topological group, `𝓝 : G → filter G` can be promoted to an\n`add_hom`.", simps]
def nhdsMulHom : MulHom G (Filter G) :=
  { toFun := 𝓝, map_mul' := fun _ _ => nhds_mul _ _ }

end

end FilterMul

instance Additive.topological_add_group {G} [h : TopologicalSpace G] [Groupₓ G] [TopologicalGroup G] :
    @TopologicalAddGroup (Additive G) h _ where
  continuous_neg := @continuous_inv G _ _ _

instance Multiplicative.topological_group {G} [h : TopologicalSpace G] [AddGroupₓ G] [TopologicalAddGroup G] :
    @TopologicalGroup (Multiplicative G) h _ where
  continuous_inv := @continuous_neg G _ _ _

namespace Units

variable [Monoidₓ α] [TopologicalSpace α] [HasContinuousMul α] [Monoidₓ β] [TopologicalSpace β] [HasContinuousMul β]

instance : TopologicalGroup (Units α) where
  continuous_inv :=
    continuous_induced_rng
      ((continuous_unop.comp (continuous_snd.comp (@continuous_embed_product α _ _))).prod_mk
        (continuous_op.comp continuous_coe))

/--  The topological group isomorphism between the units of a product of two monoids, and the product
    of the units of each monoid. -/
def homeomorph.prod_units : Homeomorph (Units (α × β)) (Units α × Units β) :=
  { MulEquiv.prodUnits with
    continuous_to_fun := by
      apply Continuous.prod_mk
      ·
        refine' continuous_induced_rng ((continuous_fst.comp Units.continuous_coe).prod_mk _)
        refine' continuous_op.comp (continuous_fst.comp _)
        simp_rw [Units.inv_eq_coe_inv]
        exact units.continuous_coe.comp continuous_inv
      ·
        refine' continuous_induced_rng ((continuous_snd.comp Units.continuous_coe).prod_mk _)
        simp_rw [Units.coe_map_inv]
        exact continuous_op.comp (continuous_snd.comp (units.continuous_coe.comp continuous_inv)),
    continuous_inv_fun := by
      refine' continuous_induced_rng (Continuous.prod_mk _ _)
      ·
        exact (units.continuous_coe.comp continuous_fst).prod_mk (units.continuous_coe.comp continuous_snd)
      ·
        refine' continuous_op.comp (units.continuous_coe.comp $ continuous_induced_rng $ Continuous.prod_mk _ _)
        ·
          exact
            (units.continuous_coe.comp (continuous_inv.comp continuous_fst)).prod_mk
              (units.continuous_coe.comp (continuous_inv.comp continuous_snd))
        ·
          exact
            continuous_op.comp
              ((units.continuous_coe.comp continuous_fst).prod_mk (units.continuous_coe.comp continuous_snd)) }

end Units

/-!
### Lattice of group topologies
We define a type class `group_topology α` which endows a group `α` with a topology such that all
group operations are continuous.

Group topologies on a fixed group `α` are ordered, by reverse inclusion. They form a complete
lattice, with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : α → β` induces `coinduced f : topological_space α → group_topology β`.

The additive version `add_group_topology α` and corresponding results are provided as well.
-/


/--  A group topology on a group `α` is a topology for which multiplication and inversion
are continuous. -/
@[ext]
structure GroupTopology (α : Type u) [Groupₓ α] extends TopologicalSpace α, TopologicalGroup α : Type u

/--  An additive group topology on an additive group `α` is a topology for which addition and
  negation are continuous. -/
@[ext]
structure AddGroupTopology (α : Type u) [AddGroupₓ α] extends TopologicalSpace α, TopologicalAddGroup α : Type u

attribute [to_additive] GroupTopology

namespace GroupTopology

@[to_additive]
instance Inhabited {α : Type u} [Groupₓ α] : Inhabited (GroupTopology α) :=
  ⟨{ toTopologicalSpace := ⊤, continuous_mul := continuous_top, continuous_inv := continuous_top }⟩

variable {γ : Type _}

@[ext, to_additive AddGroupTopology.ext]
theorem ext' [Groupₓ γ] {f g : GroupTopology γ} (h : f.is_open = g.is_open) : f = g := by
  ext
  rw [h]

/--  The ordering on group topologies on the group `γ`.
  `t ≤ s` if every set open in `s` is also open in `t` (`t` is finer than `s`). -/
@[to_additive]
instance [Groupₓ γ] : PartialOrderₓ (GroupTopology γ) :=
  PartialOrderₓ.lift to_topological_space $ ext

local notation "cont" => @Continuous _ _

@[to_additive AddGroupTopology.defInf "Infimum of a collection of additive group topologies"]
private def def_Inf [Groupₓ γ] (S : Set (GroupTopology γ)) : GroupTopology γ :=
  let Inf_S' := Inf (to_topological_space '' S)
  { toTopologicalSpace := Inf_S',
    continuous_mul := by
      apply continuous_Inf_rng
      rintro _ ⟨⟨t, tr⟩, haS, rfl⟩
      skip
      have h := continuous_Inf_dom (Set.mem_image_of_mem to_topological_space haS) continuous_id
      have h_continuous_id := @Continuous.prod_map _ _ _ _ t t Inf_S' Inf_S' _ _ h h
      have h_continuous_mul : cont (id _) t fun p : γ × γ => p.fst*p.snd := continuous_mul
      exact @Continuous.comp _ _ _ (id _) (id _) t _ _ h_continuous_mul h_continuous_id,
    continuous_inv := by
      apply continuous_Inf_rng
      rintro _ ⟨⟨t, tr⟩, haS, rfl⟩
      skip
      exact
        @Continuous.comp _ _ _ (id _) (id _) t _ _ continuous_inv
          (continuous_Inf_dom (Set.mem_image_of_mem to_topological_space haS) continuous_id) }

/--  Group topologies on `γ` form a complete lattice, with `⊥` the discrete topology and `⊤` the
indiscrete topology.

The infimum of a collection of group topologies is the topology generated by all their open sets
(which is a group topology).

The supremum of two group topologies `s` and `t` is the infimum of the family of all group
topologies contained in the intersection of `s` and `t`. -/
@[to_additive]
instance [Groupₓ γ] : CompleteSemilatticeInf (GroupTopology γ) :=
  { GroupTopology.partialOrder with inf := def_Inf,
    Inf_le := fun S a haS => by
      apply topological_space.complete_lattice.Inf_le
      use a, ⟨haS, rfl⟩,
    le_Inf := by
      intro S a hab
      apply topological_space.complete_lattice.le_Inf
      rintro _ ⟨b, hbS, rfl⟩
      exact hab b hbS }

@[to_additive]
instance [Groupₓ γ] : CompleteLattice (GroupTopology γ) :=
  completeLatticeOfCompleteSemilatticeInf _

/--   Given `f : α → β` and a topology on `α`, the coinduced group topology on `β` is the finest
topology such that `f` is continuous and `β` is a topological group. -/
@[to_additive
      "Given `f : α → β` and a topology on `α`, the coinduced additive group topology on `β`\nis the finest topology such that `f` is continuous and `β` is a topological additive group."]
def coinduced {α β : Type _} [t : TopologicalSpace α] [Groupₓ β] (f : α → β) : GroupTopology β :=
  Inf { b : GroupTopology β | TopologicalSpace.coinduced f t ≤ b.to_topological_space }

@[to_additive]
theorem coinduced_continuous {α β : Type _} [t : TopologicalSpace α] [Groupₓ β] (f : α → β) :
    cont t (coinduced f).toTopologicalSpace f := by
  rw [continuous_iff_coinduced_le]
  refine' le_Inf _
  rintro _ ⟨t', ht', rfl⟩
  exact ht'

end GroupTopology

