/-
Copyright (c) 2022 Michael Blyth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Blyth

! This file was ported from Lean 3 source module linear_algebra.projective_space.independence
! leanprover-community/mathlib commit ef55335933293309ff8c0b1d20ffffeecbe5c39f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.ProjectiveSpace.Basic

/-!
# Independence in Projective Space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define independence and dependence of families of elements in projective space.

## Implementation Details

We use an inductive definition to define the independence of points in projective
space, where the only constructor assumes an independent family of vectors from the
ambient vector space. Similarly for the definition of dependence.

## Results

- A family of elements is dependent if and only if it is not independent.
- Two elements are dependent if and only if they are equal.

# Future Work

- Define collinearity in projective space.
- Prove the axioms of a projective geometry are satisfied by the dependence relation.
- Define projective linear subspaces.
-/


variable {ι K V : Type _} [Field K] [AddCommGroup V] [Module K V] {f : ι → ℙ K V}

namespace Projectivization

#print Projectivization.Independent /-
/-- A linearly independent family of nonzero vectors gives an independent family of points
in projective space. -/
inductive Independent : (ι → ℙ K V) → Prop
  |
  mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (hl : LinearIndependent K f) :
    independent fun i => mk K (f i) (hf i)
#align projectivization.independent Projectivization.Independent
-/

/- warning: projectivization.independent_iff -> Projectivization.independent_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {K : Type.{u2}} {V : Type.{u3}} [_inst_1 : Field.{u2} K] [_inst_2 : AddCommGroup.{u3} V] [_inst_3 : Module.{u2, u3} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u3} V _inst_2)] {f : ι -> (Projectivization.{u2, u3} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3)}, Iff (Projectivization.Independent.{u1, u2, u3} ι K V _inst_1 _inst_2 _inst_3 f) (LinearIndependent.{u1, u2, u3} ι K V (Function.comp.{succ u1, succ u3, succ u3} ι (Projectivization.{u2, u3} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) V (Projectivization.rep.{u2, u3} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) f) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u3} V _inst_2) _inst_3)
but is expected to have type
  forall {ι : Type.{u3}} {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : Field.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] {f : ι -> (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3)}, Iff (Projectivization.Independent.{u3, u2, u1} ι K V _inst_1 _inst_2 _inst_3 f) (LinearIndependent.{u3, u2, u1} ι K V (Function.comp.{succ u3, succ u1, succ u1} ι (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) V (Projectivization.rep.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) f) (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3)
Case conversion may be inaccurate. Consider using '#align projectivization.independent_iff Projectivization.independent_iffₓ'. -/
/-- A family of points in a projective space is independent if and only if the representative
vectors determined by the family are linearly independent. -/
theorem independent_iff : Independent f ↔ LinearIndependent K (Projectivization.rep ∘ f) :=
  by
  refine' ⟨_, fun h => _⟩
  · rintro ⟨ff, hff, hh⟩
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert hh.units_smul a
    ext i; exact (ha i).symm
  · convert independent.mk _ _ h
    · ext; simp only [mk_rep]
    · intro i; apply rep_nonzero
#align projectivization.independent_iff Projectivization.independent_iff

/- warning: projectivization.independent_iff_complete_lattice_independent -> Projectivization.independent_iff_completeLattice_independent is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {K : Type.{u2}} {V : Type.{u3}} [_inst_1 : Field.{u2} K] [_inst_2 : AddCommGroup.{u3} V] [_inst_3 : Module.{u2, u3} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u3} V _inst_2)] {f : ι -> (Projectivization.{u2, u3} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3)}, Iff (Projectivization.Independent.{u1, u2, u3} ι K V _inst_1 _inst_2 _inst_3 f) (CompleteLattice.Independent.{succ u1, u3} ι (Submodule.{u2, u3} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u3} V _inst_2) _inst_3) (Submodule.completeLattice.{u2, u3} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u3} V _inst_2) _inst_3) (fun (i : ι) => Projectivization.submodule.{u2, u3} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3 (f i)))
but is expected to have type
  forall {ι : Type.{u3}} {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : Field.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] {f : ι -> (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3)}, Iff (Projectivization.Independent.{u3, u2, u1} ι K V _inst_1 _inst_2 _inst_3 f) (CompleteLattice.Independent.{succ u3, u1} ι (Submodule.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K (Field.toDivisionRing.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3) (Submodule.completeLattice.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K (Field.toDivisionRing.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3) (fun (i : ι) => Projectivization.submodule.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3 (f i)))
Case conversion may be inaccurate. Consider using '#align projectivization.independent_iff_complete_lattice_independent Projectivization.independent_iff_completeLattice_independentₓ'. -/
/-- A family of points in projective space is independent if and only if the family of
submodules which the points determine is independent in the lattice-theoretic sense. -/
theorem independent_iff_completeLattice_independent :
    Independent f ↔ CompleteLattice.Independent fun i => (f i).Submodule :=
  by
  refine' ⟨_, fun h => _⟩
  · rintro ⟨f, hf, hi⟩
    simpa [submodule_mk, CompleteLattice.independent_iff_linearIndependent_of_ne_zero hf]
  · rw [independent_iff]
    refine' h.linear_independent (Projectivization.submodule ∘ f) (fun i => _) fun i => _
    · simpa only [Function.comp_apply, submodule_eq] using Submodule.mem_span_singleton_self _
    · exact rep_nonzero (f i)
#align projectivization.independent_iff_complete_lattice_independent Projectivization.independent_iff_completeLattice_independent

#print Projectivization.Dependent /-
/-- A linearly dependent family of nonzero vectors gives a dependent family of points
in projective space. -/
inductive Dependent : (ι → ℙ K V) → Prop
  |
  mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (h : ¬LinearIndependent K f) :
    dependent fun i => mk K (f i) (hf i)
#align projectivization.dependent Projectivization.Dependent
-/

/- warning: projectivization.dependent_iff -> Projectivization.dependent_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {K : Type.{u2}} {V : Type.{u3}} [_inst_1 : Field.{u2} K] [_inst_2 : AddCommGroup.{u3} V] [_inst_3 : Module.{u2, u3} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u3} V _inst_2)] {f : ι -> (Projectivization.{u2, u3} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3)}, Iff (Projectivization.Dependent.{u1, u2, u3} ι K V _inst_1 _inst_2 _inst_3 f) (Not (LinearIndependent.{u1, u2, u3} ι K V (Function.comp.{succ u1, succ u3, succ u3} ι (Projectivization.{u2, u3} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) V (Projectivization.rep.{u2, u3} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) f) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u3} V _inst_2) _inst_3))
but is expected to have type
  forall {ι : Type.{u3}} {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : Field.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] {f : ι -> (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3)}, Iff (Projectivization.Dependent.{u3, u2, u1} ι K V _inst_1 _inst_2 _inst_3 f) (Not (LinearIndependent.{u3, u2, u1} ι K V (Function.comp.{succ u3, succ u1, succ u1} ι (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) V (Projectivization.rep.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) f) (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3))
Case conversion may be inaccurate. Consider using '#align projectivization.dependent_iff Projectivization.dependent_iffₓ'. -/
/-- A family of points in a projective space is dependent if and only if their
representatives are linearly dependent. -/
theorem dependent_iff : Dependent f ↔ ¬LinearIndependent K (Projectivization.rep ∘ f) :=
  by
  refine' ⟨_, fun h => _⟩
  · rintro ⟨ff, hff, hh1⟩
    contrapose! hh1
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert hh1.units_smul a⁻¹
    ext i
    simp only [← ha, inv_smul_smul, Pi.smul_apply', Pi.inv_apply, Function.comp_apply]
  · convert dependent.mk _ _ h
    · ext i; simp only [mk_rep]
    · exact fun i => rep_nonzero (f i)
#align projectivization.dependent_iff Projectivization.dependent_iff

/- warning: projectivization.dependent_iff_not_independent -> Projectivization.dependent_iff_not_independent is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {K : Type.{u2}} {V : Type.{u3}} [_inst_1 : Field.{u2} K] [_inst_2 : AddCommGroup.{u3} V] [_inst_3 : Module.{u2, u3} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u3} V _inst_2)] {f : ι -> (Projectivization.{u2, u3} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3)}, Iff (Projectivization.Dependent.{u1, u2, u3} ι K V _inst_1 _inst_2 _inst_3 f) (Not (Projectivization.Independent.{u1, u2, u3} ι K V _inst_1 _inst_2 _inst_3 f))
but is expected to have type
  forall {ι : Type.{u3}} {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : Field.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] {f : ι -> (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3)}, Iff (Projectivization.Dependent.{u3, u2, u1} ι K V _inst_1 _inst_2 _inst_3 f) (Not (Projectivization.Independent.{u3, u2, u1} ι K V _inst_1 _inst_2 _inst_3 f))
Case conversion may be inaccurate. Consider using '#align projectivization.dependent_iff_not_independent Projectivization.dependent_iff_not_independentₓ'. -/
/-- Dependence is the negation of independence. -/
theorem dependent_iff_not_independent : Dependent f ↔ ¬Independent f := by
  rw [dependent_iff, independent_iff]
#align projectivization.dependent_iff_not_independent Projectivization.dependent_iff_not_independent

/- warning: projectivization.independent_iff_not_dependent -> Projectivization.independent_iff_not_dependent is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {K : Type.{u2}} {V : Type.{u3}} [_inst_1 : Field.{u2} K] [_inst_2 : AddCommGroup.{u3} V] [_inst_3 : Module.{u2, u3} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u3} V _inst_2)] {f : ι -> (Projectivization.{u2, u3} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3)}, Iff (Projectivization.Independent.{u1, u2, u3} ι K V _inst_1 _inst_2 _inst_3 f) (Not (Projectivization.Dependent.{u1, u2, u3} ι K V _inst_1 _inst_2 _inst_3 f))
but is expected to have type
  forall {ι : Type.{u3}} {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : Field.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] {f : ι -> (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3)}, Iff (Projectivization.Independent.{u3, u2, u1} ι K V _inst_1 _inst_2 _inst_3 f) (Not (Projectivization.Dependent.{u3, u2, u1} ι K V _inst_1 _inst_2 _inst_3 f))
Case conversion may be inaccurate. Consider using '#align projectivization.independent_iff_not_dependent Projectivization.independent_iff_not_dependentₓ'. -/
/-- Independence is the negation of dependence. -/
theorem independent_iff_not_dependent : Independent f ↔ ¬Dependent f := by
  rw [dependent_iff_not_independent, Classical.not_not]
#align projectivization.independent_iff_not_dependent Projectivization.independent_iff_not_dependent

/- warning: projectivization.dependent_pair_iff_eq -> Projectivization.dependent_pair_iff_eq is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (u : Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (v : Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3), Iff (Projectivization.Dependent.{0, u1, u2} (Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))) K V _inst_1 _inst_2 _inst_3 (Matrix.vecCons.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) u (Matrix.vecCons.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) v (Matrix.vecEmpty.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3))))) (Eq.{succ u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) u v)
but is expected to have type
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : Field.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] (u : Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (v : Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3), Iff (Projectivization.Dependent.{0, u2, u1} (Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) K V _inst_1 _inst_2 _inst_3 (Matrix.vecCons.{u1} (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) u (Matrix.vecCons.{u1} (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) v (Matrix.vecEmpty.{u1} (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3))))) (Eq.{succ u1} (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) u v)
Case conversion may be inaccurate. Consider using '#align projectivization.dependent_pair_iff_eq Projectivization.dependent_pair_iff_eqₓ'. -/
/-- Two points in a projective space are dependent if and only if they are equal. -/
@[simp]
theorem dependent_pair_iff_eq (u v : ℙ K V) : Dependent ![u, v] ↔ u = v :=
  by
  simp_rw [dependent_iff_not_independent, independent_iff, linearIndependent_fin2,
    Function.comp_apply, Matrix.cons_val_one, Matrix.head_cons, Ne.def, Matrix.cons_val_zero,
    not_and, not_forall, Classical.not_not, ← mk_eq_mk_iff' K _ _ (rep_nonzero u) (rep_nonzero v),
    mk_rep, imp_iff_right_iff]
  exact Or.inl (rep_nonzero v)
#align projectivization.dependent_pair_iff_eq Projectivization.dependent_pair_iff_eq

/- warning: projectivization.independent_pair_iff_neq -> Projectivization.independent_pair_iff_neq is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (u : Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (v : Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3), Iff (Projectivization.Independent.{0, u1, u2} (Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))) K V _inst_1 _inst_2 _inst_3 (Matrix.vecCons.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Nat.succ (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) u (Matrix.vecCons.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) v (Matrix.vecEmpty.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3))))) (Ne.{succ u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) u v)
but is expected to have type
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : Field.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] (u : Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (v : Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3), Iff (Projectivization.Independent.{0, u2, u1} (Fin (Nat.succ (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) K V _inst_1 _inst_2 _inst_3 (Matrix.vecCons.{u1} (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) u (Matrix.vecCons.{u1} (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) v (Matrix.vecEmpty.{u1} (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3))))) (Ne.{succ u1} (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) u v)
Case conversion may be inaccurate. Consider using '#align projectivization.independent_pair_iff_neq Projectivization.independent_pair_iff_neqₓ'. -/
/-- Two points in a projective space are independent if and only if the points are not equal. -/
@[simp]
theorem independent_pair_iff_neq (u v : ℙ K V) : Independent ![u, v] ↔ u ≠ v := by
  rw [independent_iff_not_dependent, dependent_pair_iff_eq u v]
#align projectivization.independent_pair_iff_neq Projectivization.independent_pair_iff_neq

end Projectivization

