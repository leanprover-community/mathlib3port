/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.projections
! leanprover-community/mathlib commit 86d1873c01a723aba6788f0b9051ae3d23b4c1c3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.Faces
import Mathbin.CategoryTheory.Idempotents.Basic

/-!

# Construction of projections for the Dold-Kan correspondence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

TODO (@joelriou) continue adding the various files referenced below

In this file, we construct endomorphisms `P q : K[X] ⟶ K[X]` for all
`q : ℕ`. We study how they behave with respect to face maps with the lemmas
`higher_faces_vanish.of_P`, `higher_faces_vanish.comp_P_eq_self` and
`comp_P_eq_self_iff`.

Then, we show that they are projections (see `P_f_idem`
and `P_idem`). They are natural transformations (see `nat_trans_P`
and `P_f_naturality`) and are compatible with the application
of additive functors (see `map_P`).

By passing to the limit, these endomorphisms `P q` shall be used in `p_infty.lean`
in order to define `P_infty : K[X] ⟶ K[X]`, see `equivalence.lean` for the general
strategy of proof of the Dold-Kan equivalence.

-/


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
  CategoryTheory.SimplicialObject Opposite CategoryTheory.Idempotents

open scoped Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C] {X : SimplicialObject C}

#print AlgebraicTopology.DoldKan.P /-
/-- This is the inductive definition of the projections `P q : K[X] ⟶ K[X]`,
with `P 0 := 𝟙 _` and `P (q+1) := P q ≫ (𝟙 _ + Hσ q)`. -/
noncomputable def P : ℕ → (K[X] ⟶ K[X])
  | 0 => 𝟙 _
  | q + 1 => P q ≫ (𝟙 _ + hσ q)
#align algebraic_topology.dold_kan.P AlgebraicTopology.DoldKan.P
-/

#print AlgebraicTopology.DoldKan.P_f_0_eq /-
/-- All the `P q` coincide with `𝟙 _` in degree 0. -/
@[simp]
theorem P_f_0_eq (q : ℕ) : ((P q).f 0 : X _[0] ⟶ X _[0]) = 𝟙 _ :=
  by
  induction' q with q hq
  · rfl
  · unfold P
    simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, HomologicalComplex.id_f,
      id_comp, hq, Hσ_eq_zero, add_zero]
#align algebraic_topology.dold_kan.P_f_0_eq AlgebraicTopology.DoldKan.P_f_0_eq
-/

#print AlgebraicTopology.DoldKan.Q /-
/-- `Q q` is the complement projection associated to `P q` -/
def Q (q : ℕ) : K[X] ⟶ K[X] :=
  𝟙 _ - P q
#align algebraic_topology.dold_kan.Q AlgebraicTopology.DoldKan.Q
-/

#print AlgebraicTopology.DoldKan.P_add_Q /-
theorem P_add_Q (q : ℕ) : P q + Q q = 𝟙 K[X] := by rw [Q]; abel
#align algebraic_topology.dold_kan.P_add_Q AlgebraicTopology.DoldKan.P_add_Q
-/

#print AlgebraicTopology.DoldKan.P_add_Q_f /-
theorem P_add_Q_f (q n : ℕ) : (P q).f n + (Q q).f n = 𝟙 (X _[n]) :=
  HomologicalComplex.congr_hom (P_add_Q q) n
#align algebraic_topology.dold_kan.P_add_Q_f AlgebraicTopology.DoldKan.P_add_Q_f
-/

#print AlgebraicTopology.DoldKan.Q_zero /-
@[simp]
theorem Q_zero : (Q 0 : K[X] ⟶ _) = 0 :=
  sub_self _
#align algebraic_topology.dold_kan.Q_eq_zero AlgebraicTopology.DoldKan.Q_zero
-/

#print AlgebraicTopology.DoldKan.Q_succ /-
theorem Q_succ (q : ℕ) : (Q (q + 1) : K[X] ⟶ _) = Q q - P q ≫ hσ q := by unfold Q P;
  simp only [comp_add, comp_id]; abel
#align algebraic_topology.dold_kan.Q_eq AlgebraicTopology.DoldKan.Q_succ
-/

#print AlgebraicTopology.DoldKan.Q_f_0_eq /-
/-- All the `Q q` coincide with `0` in degree 0. -/
@[simp]
theorem Q_f_0_eq (q : ℕ) : ((Q q).f 0 : X _[0] ⟶ X _[0]) = 0 := by
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, Q, P_f_0_eq, sub_self]
#align algebraic_topology.dold_kan.Q_f_0_eq AlgebraicTopology.DoldKan.Q_f_0_eq
-/

namespace HigherFacesVanish

#print AlgebraicTopology.DoldKan.HigherFacesVanish.of_P /-
/-- This lemma expresses the vanishing of
`(P q).f (n+1) ≫ X.δ k : X _[n+1] ⟶ X _[n]` when `k≠0` and `k≥n-q+2` -/
theorem of_P : ∀ q n : ℕ, HigherFacesVanish q ((P q).f (n + 1) : X _[n + 1] ⟶ X _[n + 1])
  | 0 => fun n j hj₁ => by exfalso; have hj₂ := Fin.is_lt j; linarith
  | q + 1 => fun n => by unfold P; exact (of_P q n).induction
#align algebraic_topology.dold_kan.higher_faces_vanish.of_P AlgebraicTopology.DoldKan.HigherFacesVanish.of_P
-/

#print AlgebraicTopology.DoldKan.HigherFacesVanish.comp_P_eq_self /-
@[reassoc]
theorem comp_P_eq_self {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ) :
    φ ≫ (P q).f (n + 1) = φ := by
  induction' q with q hq
  · unfold P
    apply comp_id
  · unfold P
    simp only [comp_add, HomologicalComplex.comp_f, HomologicalComplex.add_f_apply, comp_id, ←
      assoc, hq v.of_succ, add_right_eq_self]
    by_cases hqn : n < q
    · exact v.of_succ.comp_Hσ_eq_zero hqn
    · cases' Nat.le.dest (not_lt.mp hqn) with a ha
      have hnaq : n = a + q := by linarith
      simp only [v.of_succ.comp_Hσ_eq hnaq, neg_eq_zero, ← assoc]
      have eq :=
        v ⟨a, by linarith⟩ (by simp only [hnaq, Fin.val_mk, Nat.succ_eq_add_one, add_assoc])
      simp only [Fin.succ_mk] at eq 
      simp only [Eq, zero_comp]
#align algebraic_topology.dold_kan.higher_faces_vanish.comp_P_eq_self AlgebraicTopology.DoldKan.HigherFacesVanish.comp_P_eq_self
-/

end HigherFacesVanish

#print AlgebraicTopology.DoldKan.comp_P_eq_self_iff /-
theorem comp_P_eq_self_iff {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n + 1]} :
    φ ≫ (P q).f (n + 1) = φ ↔ HigherFacesVanish q φ :=
  by
  constructor
  · intro hφ
    rw [← hφ]
    apply higher_faces_vanish.of_comp
    apply higher_faces_vanish.of_P
  · exact higher_faces_vanish.comp_P_eq_self
#align algebraic_topology.dold_kan.comp_P_eq_self_iff AlgebraicTopology.DoldKan.comp_P_eq_self_iff
-/

#print AlgebraicTopology.DoldKan.P_f_idem /-
@[simp, reassoc]
theorem P_f_idem (q n : ℕ) : ((P q).f n : X _[n] ⟶ _) ≫ (P q).f n = (P q).f n :=
  by
  cases n
  · rw [P_f_0_eq q, comp_id]
  · exact (higher_faces_vanish.of_P q n).comp_P_eq_self
#align algebraic_topology.dold_kan.P_f_idem AlgebraicTopology.DoldKan.P_f_idem
-/

#print AlgebraicTopology.DoldKan.Q_f_idem /-
@[simp, reassoc]
theorem Q_f_idem (q n : ℕ) : ((Q q).f n : X _[n] ⟶ _) ≫ (Q q).f n = (Q q).f n :=
  idem_of_id_sub_idem _ (P_f_idem q n)
#align algebraic_topology.dold_kan.Q_f_idem AlgebraicTopology.DoldKan.Q_f_idem
-/

#print AlgebraicTopology.DoldKan.P_idem /-
@[simp, reassoc]
theorem P_idem (q : ℕ) : (P q : K[X] ⟶ K[X]) ≫ P q = P q := by ext n; exact P_f_idem q n
#align algebraic_topology.dold_kan.P_idem AlgebraicTopology.DoldKan.P_idem
-/

#print AlgebraicTopology.DoldKan.Q_idem /-
@[simp, reassoc]
theorem Q_idem (q : ℕ) : (Q q : K[X] ⟶ K[X]) ≫ Q q = Q q := by ext n; exact Q_f_idem q n
#align algebraic_topology.dold_kan.Q_idem AlgebraicTopology.DoldKan.Q_idem
-/

#print AlgebraicTopology.DoldKan.natTransP /-
/-- For each `q`, `P q` is a natural transformation. -/
@[simps]
def natTransP (q : ℕ) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C
    where
  app X := P q
  naturality' X Y f := by
    induction' q with q hq
    · unfold P
      dsimp only [alternating_face_map_complex]
      rw [id_comp, comp_id]
    · unfold P
      simp only [add_comp, comp_add, assoc, comp_id, hq]
      congr 1
      rw [← assoc, hq, assoc]
      congr 1
      exact (nat_trans_Hσ q).naturality' f
#align algebraic_topology.dold_kan.nat_trans_P AlgebraicTopology.DoldKan.natTransP
-/

#print AlgebraicTopology.DoldKan.P_f_naturality /-
@[simp, reassoc]
theorem P_f_naturality (q n : ℕ) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op [n]) ≫ (P q).f n = (P q).f n ≫ f.app (op [n]) :=
  HomologicalComplex.congr_hom ((natTransP q).naturality f) n
#align algebraic_topology.dold_kan.P_f_naturality AlgebraicTopology.DoldKan.P_f_naturality
-/

#print AlgebraicTopology.DoldKan.Q_f_naturality /-
@[simp, reassoc]
theorem Q_f_naturality (q n : ℕ) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op [n]) ≫ (Q q).f n = (Q q).f n ≫ f.app (op [n]) :=
  by
  simp only [Q, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, comp_sub, P_f_naturality,
    sub_comp, sub_left_inj]
  dsimp
  simp only [comp_id, id_comp]
#align algebraic_topology.dold_kan.Q_f_naturality AlgebraicTopology.DoldKan.Q_f_naturality
-/

#print AlgebraicTopology.DoldKan.natTransQ /-
/-- For each `q`, `Q q` is a natural transformation. -/
@[simps]
def natTransQ (q : ℕ) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where app X := Q q
#align algebraic_topology.dold_kan.nat_trans_Q AlgebraicTopology.DoldKan.natTransQ
-/

#print AlgebraicTopology.DoldKan.map_P /-
theorem map_P {D : Type _} [Category D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n : ℕ) :
    G.map ((P q : K[X] ⟶ _).f n) = (P q : K[((whiskering C D).obj G).obj X] ⟶ _).f n :=
  by
  induction' q with q hq
  · unfold P
    apply G.map_id
  · unfold P
    simp only [comp_add, HomologicalComplex.comp_f, HomologicalComplex.add_f_apply, comp_id,
      functor.map_add, functor.map_comp, hq, map_Hσ]
#align algebraic_topology.dold_kan.map_P AlgebraicTopology.DoldKan.map_P
-/

#print AlgebraicTopology.DoldKan.map_Q /-
theorem map_Q {D : Type _} [Category D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n : ℕ) :
    G.map ((Q q : K[X] ⟶ _).f n) = (Q q : K[((whiskering C D).obj G).obj X] ⟶ _).f n :=
  by
  rw [← add_right_inj (G.map ((P q : K[X] ⟶ _).f n)), ← G.map_add, map_P G X q n, P_add_Q_f,
    P_add_Q_f]
  apply G.map_id
#align algebraic_topology.dold_kan.map_Q AlgebraicTopology.DoldKan.map_Q
-/

end DoldKan

end AlgebraicTopology

