import Mathbin.Algebra.Category.CommRing.Basic 
import Mathbin.Topology.Category.Top.Basic 
import Mathbin.Topology.Algebra.Ring

/-!
# Category of topological commutative rings

We introduce the category `TopCommRing` of topological commutative rings together with the relevant
forgetful functors to topological spaces and commutative rings.
-/


universe u

open CategoryTheory

/-- A bundled topological commutative ring. -/
structure TopCommRing where 
  α : Type u
  [isCommRing : CommRingₓ α]
  [isTopologicalSpace : TopologicalSpace α]
  [is_topological_ring : TopologicalRing α]

namespace TopCommRing

instance  : Inhabited TopCommRing :=
  ⟨⟨PUnit⟩⟩

instance  : CoeSort TopCommRing (Type u) :=
  ⟨TopCommRing.α⟩

attribute [instance] is_comm_ring is_topological_space is_topological_ring

instance  : category TopCommRing.{u} :=
  { Hom := fun R S => { f : R →+* S // Continuous f },
    id :=
      fun R =>
        ⟨RingHom.id R,
          by 
            runTac 
              obviously⟩,
    comp :=
      fun R S T f g =>
        ⟨g.val.comp f.val,
          by 
            cases f 
            cases g 
            dsimp 
            apply Continuous.comp <;> assumption⟩ }

instance  : concrete_category TopCommRing.{u} :=
  { forget := { obj := fun R => R, map := fun R S f => f.val }, forget_faithful := {  } }

/-- Construct a bundled `TopCommRing` from the underlying type and the appropriate typeclasses. -/
def of (X : Type u) [CommRingₓ X] [TopologicalSpace X] [TopologicalRing X] : TopCommRing :=
  ⟨X⟩

@[simp]
theorem coe_of (X : Type u) [CommRingₓ X] [TopologicalSpace X] [TopologicalRing X] : (of X : Type u) = X :=
  rfl

instance forget_topological_space (R : TopCommRing) : TopologicalSpace ((forget TopCommRing).obj R) :=
  R.is_topological_space

instance forget_comm_ring (R : TopCommRing) : CommRingₓ ((forget TopCommRing).obj R) :=
  R.is_comm_ring

instance forget_topological_ring (R : TopCommRing) : TopologicalRing ((forget TopCommRing).obj R) :=
  R.is_topological_ring

instance has_forget_to_CommRing : has_forget₂ TopCommRing CommRingₓₓ :=
  has_forget₂.mk' (fun R => CommRingₓₓ.of R) (fun x => rfl) (fun R S f => f.val) fun R S f => HEq.rfl

instance forget_to_CommRing_topological_space (R : TopCommRing) :
  TopologicalSpace ((forget₂ TopCommRing CommRingₓₓ).obj R) :=
  R.is_topological_space

/-- The forgetful functor to Top. -/
instance has_forget_to_Top : has_forget₂ TopCommRing Top :=
  has_forget₂.mk' (fun R => Top.of R) (fun x => rfl) (fun R S f => ⟨«expr⇑ » f.1, f.2⟩) fun R S f => HEq.rfl

instance forget_to_Top_comm_ring (R : TopCommRing) : CommRingₓ ((forget₂ TopCommRing Top).obj R) :=
  R.is_comm_ring

instance forget_to_Top_topological_ring (R : TopCommRing) : TopologicalRing ((forget₂ TopCommRing Top).obj R) :=
  R.is_topological_ring

/--
The forgetful functors to `Type` do not reflect isomorphisms,
but the forgetful functor from `TopCommRing` to `Top` does.
-/
instance  : reflects_isomorphisms (forget₂ TopCommRing.{u} Top.{u}) :=
  { reflects :=
      fun X Y f _ =>
        by 
          skip 
          let i_Top := as_iso ((forget₂ TopCommRing Top).map f)
          let e_Ring : X ≃+* Y := { f.1, ((forget Top).mapIso i_Top).toEquiv with  }
          exact
            ⟨⟨⟨e_Ring.symm, i_Top.inv.2⟩,
                ⟨by 
                    ext x 
                    exact e_Ring.left_inv x,
                  by 
                    ext x 
                    exact e_Ring.right_inv x⟩⟩⟩ }

end TopCommRing

