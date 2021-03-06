/-
Copyright Β© 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn
-/
import Mathbin.Topology.VectorBundle.Basic
import Mathbin.Analysis.NormedSpace.OperatorNorm

/-!
# The topological vector bundle of continuous (semi)linear maps

We define the topological vector bundle of continuous (semi)linear maps between two
vector bundles over the same base.
Given bundles `Eβ Eβ : B β Type*`, we define
`bundle.continuous_linear_map π Eβ Eβ := Ξ» x, Eβ x βSL[π] Eβ x`.
If the `Eβ` and `Eβ` are topological vector bundles with fibers `Fβ` and `Fβ`, then this will
be a topological vector bundle with fiber `Fβ βSL[π] Fβ`.
The topology is inherited from the norm-topology on, without the need to define the strong
topology on continuous linear maps between general topological vector spaces.

## Main Definitions

* `bundle.continuous_linear_map.topological_vector_bundle`: continuous semilinear maps between
  vector bundles form a vector bundle.

-/


noncomputable section

open Bundle Set ContinuousLinearMap

section Defs

variable {πβ πβ : Type _} [NormedField πβ] [NormedField πβ]

variable (Ο : πβ β+* πβ)

variable {B : Type _}

variable (Fβ : Type _) (Eβ : B β Type _) [β x, AddCommMonoidβ (Eβ x)] [β x, Module πβ (Eβ x)]

variable [β x : B, TopologicalSpace (Eβ x)]

variable (Fβ : Type _) (Eβ : B β Type _) [β x, AddCommMonoidβ (Eβ x)] [β x, Module πβ (Eβ x)]

variable [β x : B, TopologicalSpace (Eβ x)]

include Fβ Fβ

/-- The bundle of continuous `Ο`-semilinear maps between the topological vector bundles `Eβ` and
`Eβ`. This is a type synonym for `Ξ» x, Eβ x βSL[Ο] Eβ x`.

We intentionally add `Fβ` and `Fβ` as arguments to this type, so that instances on this type
(that depend on `Fβ` and `Fβ`) actually refer to `Fβ` and `Fβ`. -/
-- In this definition we require the scalar rings `πβ` and `πβ` to be normed fields, although
-- something much weaker (maybe `comm_semiring`) would suffice mathematically -- this is because of
-- a typeclass inference bug with pi-types:
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/vector.20bundles.20--.20typeclass.20inference.20issue
@[nolint unused_arguments]
def Bundle.ContinuousLinearMap (x : B) : Type _ :=
  Eβ x βSL[Ο] Eβ x deriving Inhabited

instance Bundle.ContinuousLinearMap.addMonoidHomClass (x : B) :
    AddMonoidHomClass (Bundle.ContinuousLinearMap Ο Fβ Eβ Fβ Eβ x) (Eβ x) (Eβ x) := by
  delta_instance bundle.continuous_linear_map

variable [β x, HasContinuousAdd (Eβ x)]

instance (x : B) : AddCommMonoidβ (Bundle.ContinuousLinearMap Ο Fβ Eβ Fβ Eβ x) := by
  delta_instance bundle.continuous_linear_map

variable [β x, HasContinuousSmul πβ (Eβ x)]

instance (x : B) : Module πβ (Bundle.ContinuousLinearMap Ο Fβ Eβ Fβ Eβ x) := by
  delta_instance bundle.continuous_linear_map

end Defs

variable {πβ : Type _} [NondiscreteNormedField πβ] {πβ : Type _} [NondiscreteNormedField πβ] (Ο : πβ β+* πβ)

variable {B : Type _} [TopologicalSpace B]

variable (Fβ : Type _) [NormedGroup Fβ] [NormedSpace πβ Fβ] (Eβ : B β Type _) [β x, AddCommMonoidβ (Eβ x)]
  [β x, Module πβ (Eβ x)] [TopologicalSpace (TotalSpace Eβ)]

variable (Fβ : Type _) [NormedGroup Fβ] [NormedSpace πβ Fβ] (Eβ : B β Type _) [β x, AddCommMonoidβ (Eβ x)]
  [β x, Module πβ (Eβ x)] [TopologicalSpace (TotalSpace Eβ)]

namespace TopologicalVectorBundle

variable {Fβ Eβ Fβ Eβ} (eβ eβ' : Trivialization πβ Fβ Eβ) (eβ eβ' : Trivialization πβ Fβ Eβ)

variable [RingHomIsometric Ο]

namespace Pretrivialization

/-- Assume `eα΅’` and `eα΅’'` are trivializations of the bundles `Eα΅’` over base `B` with fiber `Fα΅’`
(`i β {1,2}`), then `continuous_linear_map_coord_change Ο eβ eβ' eβ eβ'` is the coordinate change
function between the two induced (pre)trivializations
`pretrivialization.continuous_linear_map Ο eβ eβ` and
`pretrivialization.continuous_linear_map Ο eβ' eβ'` of `bundle.continuous_linear_map`. -/
def continuousLinearMapCoordChange (b : B) : (Fβ βSL[Ο] Fβ) βL[πβ] Fβ βSL[Ο] Fβ :=
  ((eβ'.coordChange eβ b).symm.arrowCongrSL (eβ.coordChange eβ' b) : (Fβ βSL[Ο] Fβ) βL[πβ] Fβ βSL[Ο] Fβ)

variable {Ο eβ eβ' eβ eβ'}

variable [β x : B, TopologicalSpace (Eβ x)] [TopologicalVectorBundle πβ Fβ Eβ]

variable [β x : B, TopologicalSpace (Eβ x)] [TopologicalVectorBundle πβ Fβ Eβ]

theorem continuous_on_continuous_linear_map_coord_change (heβ : eβ β TrivializationAtlas πβ Fβ Eβ)
    (heβ' : eβ' β TrivializationAtlas πβ Fβ Eβ) (heβ : eβ β TrivializationAtlas πβ Fβ Eβ)
    (heβ' : eβ' β TrivializationAtlas πβ Fβ Eβ) :
    ContinuousOn (continuousLinearMapCoordChange Ο eβ eβ' eβ eβ')
      (eβ.BaseSet β© eβ.BaseSet β© (eβ'.BaseSet β© eβ'.BaseSet)) :=
  by
  have hβ := (compSL Fβ Fβ Fβ Ο (RingHom.id πβ)).Continuous
  have hβ := (ContinuousLinearMap.flip (compSL Fβ Fβ Fβ (RingHom.id πβ) Ο)).Continuous
  have hβ := continuous_on_coord_change eβ' heβ' eβ heβ
  have hβ := continuous_on_coord_change eβ heβ eβ' heβ'
  refine' ((hβ.comp_continuous_on (hβ.mono _)).clm_comp (hβ.comp_continuous_on (hβ.mono _))).congr _
  Β· mfld_set_tac
    
  Β· mfld_set_tac
    
  Β· intro b hb
    ext L v
    simp only [β continuous_linear_map_coord_change, β ContinuousLinearEquiv.coe_coe, β
      ContinuousLinearEquiv.arrow_congrSL_apply, β comp_apply, β Function.comp, β compSL_apply, β flip_apply, β
      ContinuousLinearEquiv.symm_symm]
    

variable (Ο eβ eβ' eβ eβ')

variable [β x, HasContinuousAdd (Eβ x)] [β x, HasContinuousSmul πβ (Eβ x)]

/-- Given trivializations `eβ`, `eβ` for vector bundles `Eβ`, `Eβ` over a base `B`,
`pretrivialization.continuous_linear_map Ο eβ eβ` is the induced pretrivialization for the
continuous `Ο`-semilinear maps from `Eβ` to `Eβ`. That is, the map which will later become a
trivialization, after the bundle of continuous semilinear maps is equipped with the right
topological vector bundle structure. -/
def continuousLinearMap : Pretrivialization πβ (Fβ βSL[Ο] Fβ) (Bundle.ContinuousLinearMap Ο Fβ Eβ Fβ Eβ) where
  toFun := fun p => β¨p.1, (eβ.continuousLinearMapAt p.1).comp <| p.2.comp <| eβ.symmL p.1β©
  invFun := fun p => β¨p.1, (eβ.symmL p.1).comp <| p.2.comp <| eβ.continuousLinearMapAt p.1β©
  Source := Bundle.TotalSpace.proj β»ΒΉ' (eβ.BaseSet β© eβ.BaseSet)
  Target := (eβ.BaseSet β© eβ.BaseSet) ΓΛ’ (Set.Univ : Set (Fβ βSL[Ο] Fβ))
  map_source' := fun β¨x, Lβ© h => β¨h, Set.mem_univ _β©
  map_target' := fun β¨x, fβ© h => h.1
  left_inv' := fun β¨x, Lβ© β¨hβ, hββ© => by
    simp_rw [Sigma.mk.inj_iff, eq_self_iff_true, heq_iff_eq, true_andβ]
    ext v
    simp only [β comp_apply, β trivialization.symmL_continuous_linear_map_at, β hβ, β hβ]
  right_inv' := fun β¨x, fβ© β¨β¨hβ, hββ©, _β© => by
    simp_rw [Prod.mk.inj_iff, eq_self_iff_true, true_andβ]
    ext v
    simp only [β comp_apply, β trivialization.continuous_linear_map_at_symmL, β hβ, β hβ]
  open_target := (eβ.open_base_set.inter eβ.open_base_set).Prod is_open_univ
  BaseSet := eβ.BaseSet β© eβ.BaseSet
  open_base_set := eβ.open_base_set.inter eβ.open_base_set
  source_eq := rfl
  target_eq := rfl
  proj_to_fun := fun β¨x, fβ© h => rfl
  linear' := fun x h =>
    { map_add := fun L L' => by
        simp_rw [add_comp, comp_add],
      map_smul := fun c L => by
        simp_rw [smul_comp, comp_smulββ, RingHom.id_apply] }

theorem continuous_linear_map_apply (p : TotalSpace (Bundle.ContinuousLinearMap Ο Fβ Eβ Fβ Eβ)) :
    (continuousLinearMap Ο eβ eβ) p = β¨p.1, (eβ.continuousLinearMapAt p.1).comp <| p.2.comp <| eβ.symmL p.1β© :=
  rfl

theorem continuous_linear_map_symm_apply (p : B Γ (Fβ βSL[Ο] Fβ)) :
    (continuousLinearMap Ο eβ eβ).toLocalEquiv.symm p =
      β¨p.1, (eβ.symmL p.1).comp <| p.2.comp <| eβ.continuousLinearMapAt p.1β© :=
  rfl

theorem continuous_linear_map_symm_apply' {b : B} (hb : b β eβ.BaseSet β© eβ.BaseSet) (L : Fβ βSL[Ο] Fβ) :
    (continuousLinearMap Ο eβ eβ).symm b L = (eβ.symmL b).comp (L.comp <| eβ.continuousLinearMapAt b) := by
  rw [symm_apply]
  rfl
  exact hb

theorem continuous_linear_map_coord_change_apply (b : B)
    (hb : b β eβ.BaseSet β© eβ.BaseSet β© (eβ'.BaseSet β© eβ'.BaseSet)) (L : Fβ βSL[Ο] Fβ) :
    continuousLinearMapCoordChange Ο eβ eβ' eβ eβ' b L =
      (continuousLinearMap Ο eβ' eβ' (totalSpaceMk b ((continuousLinearMap Ο eβ eβ).symm b L))).2 :=
  by
  ext v
  simp_rw [continuous_linear_map_coord_change, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.arrow_congrSL_apply,
    continuous_linear_map_apply, continuous_linear_map_symm_apply' Ο eβ eβ hb.1, comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_symm, trivialization.continuous_linear_map_at_apply,
    trivialization.symmL_apply]
  dsimp' only [β total_space_mk]
  rw [eβ.coord_change_apply eβ', eβ'.coord_change_apply eβ, eβ.coe_linear_map_at_of_mem hb.1.1,
    eβ'.coe_linear_map_at_of_mem hb.2.2]
  exacts[β¨hb.2.1, hb.1.1β©, β¨hb.1.2, hb.2.2β©]

end Pretrivialization

open Pretrivialization

variable (Fβ Eβ Fβ Eβ)

variable [β x : B, TopologicalSpace (Eβ x)] [TopologicalVectorBundle πβ Fβ Eβ]

variable [β x : B, TopologicalSpace (Eβ x)] [TopologicalVectorBundle πβ Fβ Eβ]

variable [β x, HasContinuousAdd (Eβ x)] [β x, HasContinuousSmul πβ (Eβ x)]

/-- The continuous `Ο`-semilinear maps between two topological vector bundles form a
`topological_vector_prebundle` (this is an auxiliary construction for the
`topological_vector_bundle` instance, in which the pretrivializations are collated but no topology
on the total space is yet provided). -/
def _root_.bundle.continuous_linear_map.topological_vector_prebundle :
    TopologicalVectorPrebundle πβ (Fβ βSL[Ο] Fβ) (Bundle.ContinuousLinearMap Ο Fβ Eβ Fβ Eβ) where
  PretrivializationAtlas :=
    Image2 (fun eβ eβ => Pretrivialization.continuousLinearMap Ο eβ eβ) (TrivializationAtlas πβ Fβ Eβ)
      (TrivializationAtlas πβ Fβ Eβ)
  pretrivializationAt := fun x =>
    Pretrivialization.continuousLinearMap Ο (trivializationAt πβ Fβ Eβ x) (trivializationAt πβ Fβ Eβ x)
  mem_base_pretrivialization_at := fun x =>
    β¨mem_base_set_trivialization_at πβ Fβ Eβ x, mem_base_set_trivialization_at πβ Fβ Eβ xβ©
  pretrivialization_mem_atlas := fun x =>
    β¨_, _, trivialization_mem_atlas πβ Fβ Eβ x, trivialization_mem_atlas πβ Fβ Eβ x, rflβ©
  exists_coord_change := by
    rintro _ β¨eβ, eβ, heβ, heβ, rflβ© _ β¨eβ', eβ', heβ', heβ', rflβ©
    exact
      β¨continuous_linear_map_coord_change Ο eβ eβ' eβ eβ',
        continuous_on_continuous_linear_map_coord_change heβ heβ' heβ heβ',
        continuous_linear_map_coord_change_apply Ο eβ eβ' eβ eβ'β©

/-- Topology on the continuous `Ο`-semilinear_maps between the respective fibers at a point of two
"normable" vector bundles over the same base. Here "normable" means that the bundles have fibers
modelled on normed spaces `Fβ`, `Fβ` respectively.  The topology we put on the continuous
`Ο`-semilinear_maps is the topology coming from the operator norm on maps from `Fβ` to `Fβ`. -/
instance (x : B) : TopologicalSpace (Bundle.ContinuousLinearMap Ο Fβ Eβ Fβ Eβ x) :=
  (Bundle.ContinuousLinearMap.topologicalVectorPrebundle Ο Fβ Eβ Fβ Eβ).fiberTopology x

/-- Topology on the total space of the continuous `Ο`-semilinear_maps between two "normable" vector
bundles over the same base. -/
instance : TopologicalSpace (TotalSpace (Bundle.ContinuousLinearMap Ο Fβ Eβ Fβ Eβ)) :=
  (Bundle.ContinuousLinearMap.topologicalVectorPrebundle Ο Fβ Eβ Fβ Eβ).totalSpaceTopology

/-- The continuous `Ο`-semilinear_maps between two vector bundles form a vector bundle. -/
instance _root_.bundle.continuous_linear_map.topological_vector_bundle :
    TopologicalVectorBundle πβ (Fβ βSL[Ο] Fβ) (Bundle.ContinuousLinearMap Ο Fβ Eβ Fβ Eβ) :=
  (Bundle.ContinuousLinearMap.topologicalVectorPrebundle Ο Fβ Eβ Fβ Eβ).toTopologicalVectorBundle

variable {Fβ Eβ Fβ Eβ}

/-- Given trivializations `eβ`, `eβ` in the atlas for vector bundles `Eβ`, `Eβ` over a base `B`,
the induced trivialization for the continuous `Ο`-semilinear maps from `Eβ` to `Eβ`,
whose base set is `eβ.base_set β© eβ.base_set`. -/
def Trivialization.continuousLinearMap (heβ : eβ β TrivializationAtlas πβ Fβ Eβ)
    (heβ : eβ β TrivializationAtlas πβ Fβ Eβ) :
    Trivialization πβ (Fβ βSL[Ο] Fβ) (Bundle.ContinuousLinearMap Ο Fβ Eβ Fβ Eβ) :=
  (Bundle.ContinuousLinearMap.topologicalVectorPrebundle Ο Fβ Eβ Fβ Eβ).trivializationOfMemPretrivializationAtlas
    (mem_image2_of_mem heβ heβ)

variable {eβ eβ}

@[simp]
theorem Trivialization.base_set_continuous_linear_map (heβ : eβ β TrivializationAtlas πβ Fβ Eβ)
    (heβ : eβ β TrivializationAtlas πβ Fβ Eβ) :
    (eβ.ContinuousLinearMap Ο eβ heβ heβ).BaseSet = eβ.BaseSet β© eβ.BaseSet :=
  rfl

theorem Trivialization.continuous_linear_map_apply (heβ : eβ β TrivializationAtlas πβ Fβ Eβ)
    (heβ : eβ β TrivializationAtlas πβ Fβ Eβ) (p : TotalSpace (Bundle.ContinuousLinearMap Ο Fβ Eβ Fβ Eβ)) :
    eβ.ContinuousLinearMap Ο eβ heβ heβ p = β¨p.1, (eβ.continuousLinearMapAt p.1).comp <| p.2.comp <| eβ.symmL p.1β© :=
  rfl

end TopologicalVectorBundle

