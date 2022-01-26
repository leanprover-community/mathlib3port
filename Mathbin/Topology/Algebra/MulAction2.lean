import Mathbin.Topology.Homeomorph
import Mathbin.GroupTheory.GroupAction.Basic

/-!
# Monoid actions continuous in the second variable

In this file we define class `has_continuous_smul₂`. We say `has_continuous_smul₂ Γ T` if `Γ` acts
on `T` and for each `γ`, the map `x ↦ γ • x` is continuous. (This differs from
`has_continuous_smul`, which requires simultaneous continuity in both variables.)

## Main definitions

* `has_continuous_smul₂ Γ T` : typeclass saying that the map `x ↦ γ • x` is continuous on `T`;
* `properly_discontinuous_smul`: says that the scalar multiplication `(•) : Γ → T → T`
  is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely
  many `γ:Γ` move `K` to have nontrivial intersection with `L`.
* `homeomorph.smul`: scalar multiplication by an element of a group `Γ` acting on `T`
  is a homeomorphism of `T`.

## Main results

* `is_open_map_quotient_mk_mul` : The quotient map by a group action is open.
* `t2_space_of_properly_discontinuous_smul_of_t2_space` : The quotient by a discontinuous group
  action of a locally compact t2 space is t2.

## Tags

Hausdorff, discrete group, properly discontinuous, quotient space

-/


open_locale TopologicalSpace

open Filter Set

attribute [local instance] MulAction.orbitRel

/-- Class `has_continuous_smul₂ Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of multiplicative
actions, including (semi)modules and algebras.
-/
class HasContinuousSmul₂ (Γ : Type _) (T : Type _) [TopologicalSpace T] [HasScalar Γ T] : Prop where
  continuous_smul₂ : ∀ γ : Γ, Continuous fun x : T => γ • x

/-- Class `has_continuous_vadd₂ Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of additive actions,
including (semi)modules and algebras.
-/
class HasContinuousVadd₂ (Γ : Type _) (T : Type _) [TopologicalSpace T] [HasVadd Γ T] : Prop where
  continuous_vadd₂ : ∀ γ : Γ, Continuous fun x : T => γ +ᵥ x

attribute [to_additive HasContinuousVadd₂] HasContinuousSmul₂

export HasContinuousSmul₂ (continuous_smul₂)

export HasContinuousVadd₂ (continuous_vadd₂)

/-- Class `properly_discontinuous_smul Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ:Γ` move `K` to have nontrivial intersection with `L`.
-/
class ProperlyDiscontinuousSmul (Γ : Type _) (T : Type _) [TopologicalSpace T] [HasScalar Γ T] : Prop where
  finite_disjoint_inter_image :
    ∀ {K L : Set T}, IsCompact K → IsCompact L → Set.Finite { γ : Γ | (· • ·) γ '' K ∩ L ≠ ∅ }

/-- Class `properly_discontinuous_vadd Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ:Γ` move `K` to have nontrivial intersection with `L`.
-/
class ProperlyDiscontinuousVadd (Γ : Type _) (T : Type _) [TopologicalSpace T] [HasVadd Γ T] : Prop where
  finite_disjoint_inter_image :
    ∀ {K L : Set T}, IsCompact K → IsCompact L → Set.Finite { γ : Γ | (· +ᵥ ·) γ '' K ∩ L ≠ ∅ }

attribute [to_additive] ProperlyDiscontinuousSmul

variable {Γ : Type _} [Groupₓ Γ] {T : Type _} [TopologicalSpace T] [MulAction Γ T]

/-- A finite group action is always properly discontinuous
-/
@[to_additive]
instance (priority := 100) Fintype.properly_discontinuous_smul [Fintype Γ] : ProperlyDiscontinuousSmul Γ T where
  finite_disjoint_inter_image := fun _ _ _ _ => Set.Finite.of_fintype _

export ProperlyDiscontinuousSmul (finite_disjoint_inter_image)

export ProperlyDiscontinuousVadd (finite_disjoint_inter_image)

/-- The homeomorphism given by scalar multiplication by a given element of a group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
def Homeomorph.smul {T : Type _} [TopologicalSpace T] {Γ : Type _} [Groupₓ Γ] [MulAction Γ T] [HasContinuousSmul₂ Γ T]
    (γ : Γ) : T ≃ₜ T where
  toEquiv := MulAction.toPermHom Γ T γ
  continuous_to_fun := continuous_smul₂ γ
  continuous_inv_fun := continuous_smul₂ γ⁻¹

/-- The homeomorphism given by affine-addition by an element of an additive group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
def Homeomorph.vadd {T : Type _} [TopologicalSpace T] {Γ : Type _} [AddGroupₓ Γ] [AddAction Γ T]
    [HasContinuousVadd₂ Γ T] (γ : Γ) : T ≃ₜ T where
  toEquiv := AddAction.toPermHom T Γ γ
  continuous_to_fun := continuous_vadd₂ γ
  continuous_inv_fun := continuous_vadd₂ (-γ)

attribute [to_additive Homeomorph.vadd] Homeomorph.smul

/-- The quotient map by a group action is open. -/
@[to_additive]
theorem is_open_map_quotient_mk_mul [HasContinuousSmul₂ Γ T] :
    IsOpenMap (Quotientₓ.mk : T → Quotientₓ (MulAction.orbitRel Γ T)) := by
  intro U hU
  rw [is_open_coinduced, MulAction.quotient_preimage_image_eq_union_mul U]
  exact is_open_Union fun γ => (Homeomorph.smul γ).IsOpenMap U hU

/-- The quotient by a discontinuous group action of a locally compact t2 space is t2. -/
@[to_additive]
instance (priority := 100) t2_space_of_properly_discontinuous_smul_of_t2_space [T2Space T] [LocallyCompactSpace T]
    [HasContinuousSmul₂ Γ T] [ProperlyDiscontinuousSmul Γ T] : T2Space (Quotientₓ (MulAction.orbitRel Γ T)) := by
  set Q := Quotientₓ (MulAction.orbitRel Γ T)
  rw [t2_space_iff_nhds]
  let f : T → Q := Quotientₓ.mk
  have f_op : IsOpenMap f := is_open_map_quotient_mk_mul
  rintro ⟨x₀⟩ ⟨y₀⟩ (hxy : f x₀ ≠ f y₀)
  show ∃ U ∈ 𝓝 (f x₀), ∃ V ∈ 𝓝 (f y₀), U ∩ V = ∅
  have hx₀y₀ : x₀ ≠ y₀ := ne_of_apply_ne _ hxy
  have hγx₀y₀ : ∀ γ : Γ, γ • x₀ ≠ y₀ := not_exists.mp (mt Quotientₓ.sound hxy.symm : _)
  obtain ⟨K₀, L₀, K₀_in, L₀_in, hK₀, hL₀, hK₀L₀⟩ := t2_separation_compact_nhds hx₀y₀
  let bad_Γ_set := { γ : Γ | (· • ·) γ '' K₀ ∩ L₀ ≠ ∅ }
  have bad_Γ_finite : bad_Γ_set.finite := finite_disjoint_inter_image hK₀ hL₀
  choose u v hu hv u_v_disjoint using fun γ => t2_separation_nhds (hγx₀y₀ γ)
  let U₀₀ := ⋂ γ ∈ bad_Γ_set, (· • ·) γ ⁻¹' u γ
  let U₀ := U₀₀ ∩ K₀
  let V₀₀ := ⋂ γ ∈ bad_Γ_set, v γ
  let V₀ := V₀₀ ∩ L₀
  have U_nhds : f '' U₀ ∈ 𝓝 (f x₀) := by
    apply f_op.image_mem_nhds (inter_mem ((bInter_mem bad_Γ_finite).mpr fun γ hγ => _) K₀_in)
    exact (HasContinuousSmul₂.continuous_smul₂ γ).ContinuousAt (hu γ)
  have V_nhds : f '' V₀ ∈ 𝓝 (f y₀) :=
    f_op.image_mem_nhds (inter_mem ((bInter_mem bad_Γ_finite).mpr fun γ hγ => hv γ) L₀_in)
  refine' ⟨f '' U₀, U_nhds, f '' V₀, V_nhds, _⟩
  rw [MulAction.image_inter_image_iff]
  rintro x ⟨x_in_U₀₀, x_in_K₀⟩ γ
  by_cases' H : γ ∈ bad_Γ_set
  · rintro ⟨h, -⟩
    exact
      eq_empty_iff_forall_not_mem.mp (u_v_disjoint γ) (γ • x) ⟨(mem_Inter₂.mp x_in_U₀₀ γ H : _), mem_Inter₂.mp h γ H⟩
    
  · rintro ⟨-, h'⟩
    simp only [image_smul, not_not, mem_set_of_eq, Ne.def] at H
    exact eq_empty_iff_forall_not_mem.mp H (γ • x) ⟨mem_image_of_mem _ x_in_K₀, h'⟩
    

