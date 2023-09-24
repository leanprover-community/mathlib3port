/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Algebra.Homology.Homotopy
import AlgebraicTopology.DoldKan.Notations

#align_import algebraic_topology.dold_kan.homotopies from "leanprover-community/mathlib"@"86d1873c01a723aba6788f0b9051ae3d23b4c1c3"

/-!

# Construction of homotopies for the Dold-Kan correspondence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

TODO (@joelriou) continue adding the various files referenced below

(The general strategy of proof of the Dold-Kan correspondence is explained
in `equivalence.lean`.)

The purpose of the files `homotopies.lean`, `faces.lean`, `projections.lean`
and `p_infty.lean` is to construct an idempotent endomorphism
`P_infty : K[X] ⟶ K[X]` of the alternating face map complex
for each `X : simplicial_object C` when `C` is a preadditive category.
In the case `C` is abelian, this `P_infty` shall be the projection on the
normalized Moore subcomplex of `K[X]` associated to the decomposition of the
complex `K[X]` as a direct sum of this normalized subcomplex and of the
degenerate subcomplex.

In `p_infty.lean`, this endomorphism `P_infty` shall be obtained by
passing to the limit idempotent endomorphisms `P q` for all `(q : ℕ)`.
These endomorphisms `P q` are defined by induction. The idea is to
start from the identity endomorphism `P 0` of `K[X]` and to ensure by
induction that the `q` higher face maps (except $d_0$) vanish on the
image of `P q`. Then, in a certain degree `n`, the image of `P q` for
a big enough `q` will be contained in the normalized subcomplex. This
construction is done in `projections.lean`.

It would be easy to define the `P q` degreewise (similarly as it is done
in *Simplicial Homotopy Theory* by Goerrs-Jardine p. 149), but then we would
have to prove that they are compatible with the differential (i.e. they
are chain complex maps), and also that they are homotopic to the identity.
These two verifications are quite technical. In order to reduce the number
of such technical lemmas, the strategy that is followed here is to define
a series of null homotopic maps `Hσ q` (attached to families of maps `hσ`)
and use these in order to construct `P q` : the endomorphisms `P q`
shall basically be obtained by altering the identity endomorphism by adding
null homotopic maps, so that we get for free that they are morphisms
of chain complexes and that they are homotopic to the identity. The most
technical verifications that are needed about the null homotopic maps `Hσ`
are obtained in `faces.lean`.

In this file `homotopies.lean`, we define the null homotopic maps
`Hσ q : K[X] ⟶ K[X]`, show that they are natural (see `nat_trans_Hσ`) and
compatible the application of additive functors (see `map_Hσ`).

## References
* [Albrecht Dold, *Homology of Symmetric Products and Other Functors of Complexes*][dold1958]
* [Paul G. Goerss, John F. Jardine, *Simplical Homotopy Theory*][goerss-jardine-2009]

-/


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Limits

open CategoryTheory.Preadditive

open CategoryTheory.SimplicialObject

open Homotopy

open Opposite

open scoped Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C]

variable {X : SimplicialObject C}

#print AlgebraicTopology.DoldKan.c /-
/-- As we are using chain complexes indexed by `ℕ`, we shall need the relation
`c` such `c m n` if and only if `n+1=m`. -/
abbrev c :=
  ComplexShape.down ℕ
#align algebraic_topology.dold_kan.c AlgebraicTopology.DoldKan.c
-/

#print AlgebraicTopology.DoldKan.c_mk /-
/-- Helper when we need some `c.rel i j` (i.e. `complex_shape.down ℕ`),
e.g. `c_mk n (n+1) rfl` -/
theorem c_mk (i j : ℕ) (h : j + 1 = i) : c.Rel i j :=
  ComplexShape.down_mk i j h
#align algebraic_topology.dold_kan.c_mk AlgebraicTopology.DoldKan.c_mk
-/

#print AlgebraicTopology.DoldKan.cs_down_0_not_rel_left /-
/-- This lemma is meant to be used with `null_homotopic_map'_f_of_not_rel_left` -/
theorem cs_down_0_not_rel_left (j : ℕ) : ¬c.Rel 0 j :=
  by
  intro hj
  dsimp at hj 
  apply Nat.not_succ_le_zero j
  rw [Nat.succ_eq_add_one, hj]
#align algebraic_topology.dold_kan.cs_down_0_not_rel_left AlgebraicTopology.DoldKan.cs_down_0_not_rel_left
-/

#print AlgebraicTopology.DoldKan.hσ /-
/-- The sequence of maps which gives the null homotopic maps `Hσ` that shall be in
the inductive construction of the projections `P q : K[X] ⟶ K[X]` -/
def hσ (q : ℕ) (n : ℕ) : X _[n] ⟶ X _[n + 1] :=
  if n < q then 0 else (-1 : ℤ) ^ (n - q) • X.σ ⟨n - q, Nat.sub_lt_succ n q⟩
#align algebraic_topology.dold_kan.hσ AlgebraicTopology.DoldKan.hσ
-/

#print AlgebraicTopology.DoldKan.hσ' /-
/-- We can turn `hσ` into a datum that can be passed to `null_homotopic_map'`. -/
def hσ' (q : ℕ) : ∀ n m, c.Rel m n → (K[X].pt n ⟶ K[X].pt m) := fun n m hnm =>
  hσ q n ≫ eqToHom (by congr)
#align algebraic_topology.dold_kan.hσ' AlgebraicTopology.DoldKan.hσ'
-/

#print AlgebraicTopology.DoldKan.hσ'_eq_zero /-
theorem hσ'_eq_zero {q n m : ℕ} (hnq : n < q) (hnm : c.Rel m n) :
    (hσ' q n m hnm : X _[n] ⟶ X _[m]) = 0 := by simp only [hσ', hσ]; split_ifs; exact zero_comp
#align algebraic_topology.dold_kan.hσ'_eq_zero AlgebraicTopology.DoldKan.hσ'_eq_zero
-/

#print AlgebraicTopology.DoldKan.hσ'_eq /-
theorem hσ'_eq {q n a m : ℕ} (ha : n = a + q) (hnm : c.Rel m n) :
    (hσ' q n m hnm : X _[n] ⟶ X _[m]) =
      ((-1 : ℤ) ^ a • X.σ ⟨a, Nat.lt_succ_iff.mpr (Nat.le.intro (Eq.symm ha))⟩) ≫
        eqToHom (by congr) :=
  by
  simp only [hσ', hσ]
  split_ifs
  · exfalso; linarith
  · have h' := tsub_eq_of_eq_add ha
    congr
#align algebraic_topology.dold_kan.hσ'_eq AlgebraicTopology.DoldKan.hσ'_eq
-/

#print AlgebraicTopology.DoldKan.hσ'_eq' /-
theorem hσ'_eq' {q n a : ℕ} (ha : n = a + q) :
    (hσ' q n (n + 1) rfl : X _[n] ⟶ X _[n + 1]) =
      (-1 : ℤ) ^ a • X.σ ⟨a, Nat.lt_succ_iff.mpr (Nat.le.intro (Eq.symm ha))⟩ :=
  by rw [hσ'_eq ha rfl, eq_to_hom_refl, comp_id]
#align algebraic_topology.dold_kan.hσ'_eq' AlgebraicTopology.DoldKan.hσ'_eq'
-/

/- warning: algebraic_topology.dold_kan.Hσ clashes with algebraic_topology.dold_kan.hσ -> AlgebraicTopology.DoldKan.hσ
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.Hσ AlgebraicTopology.DoldKan.hσₓ'. -/
#print AlgebraicTopology.DoldKan.hσ /-
/-- The null homotopic map $(hσ q) ∘ d + d ∘ (hσ q)$ -/
def hσ (q : ℕ) : K[X] ⟶ K[X] :=
  nullHomotopicMap' (hσ' q)
#align algebraic_topology.dold_kan.Hσ AlgebraicTopology.DoldKan.hσ
-/

#print AlgebraicTopology.DoldKan.homotopyHσToZero /-
/-- `Hσ` is null homotopic -/
def homotopyHσToZero (q : ℕ) : Homotopy (hσ q : K[X] ⟶ K[X]) 0 :=
  nullHomotopy' (hσ' q)
#align algebraic_topology.dold_kan.homotopy_Hσ_to_zero AlgebraicTopology.DoldKan.homotopyHσToZero
-/

#print AlgebraicTopology.DoldKan.Hσ_eq_zero /-
/-- In degree `0`, the null homotopic map `Hσ` is zero. -/
theorem Hσ_eq_zero (q : ℕ) : (hσ q : K[X] ⟶ K[X]).f 0 = 0 :=
  by
  unfold Hσ
  rw [null_homotopic_map'_f_of_not_rel_left (c_mk 1 0 rfl) cs_down_0_not_rel_left]
  cases q
  · rw [hσ'_eq (show 0 = 0 + 0 by rfl) (c_mk 1 0 rfl)]
    simp only [pow_zero, Fin.mk_zero, one_zsmul, eq_to_hom_refl, category.comp_id]
    erw [ChainComplex.of_d]
    simp only [alternating_face_map_complex.obj_d, Fin.sum_univ_two, Fin.val_zero, pow_zero,
      one_zsmul, Fin.val_one, pow_one, comp_add, neg_smul, one_zsmul, comp_neg, add_neg_eq_zero]
    erw [δ_comp_σ_self, δ_comp_σ_succ]
  · rw [hσ'_eq_zero (Nat.succ_pos q) (c_mk 1 0 rfl), zero_comp]
#align algebraic_topology.dold_kan.Hσ_eq_zero AlgebraicTopology.DoldKan.Hσ_eq_zero
-/

#print AlgebraicTopology.DoldKan.hσ'_naturality /-
/-- The maps `hσ' q n m hnm` are natural on the simplicial object -/
theorem hσ'_naturality (q : ℕ) (n m : ℕ) (hnm : c.Rel m n) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op [n]) ≫ hσ' q n m hnm = hσ' q n m hnm ≫ f.app (op [m]) :=
  by
  have h : n + 1 = m := hnm
  subst h
  simp only [hσ', eq_to_hom_refl, comp_id]
  unfold hσ
  split_ifs
  · rw [zero_comp, comp_zero]
  · simp only [zsmul_comp, comp_zsmul]
    erw [f.naturality]
    rfl
#align algebraic_topology.dold_kan.hσ'_naturality AlgebraicTopology.DoldKan.hσ'_naturality
-/

#print AlgebraicTopology.DoldKan.natTransHσ /-
/-- For each q, `Hσ q` is a natural transformation. -/
def natTransHσ (q : ℕ) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C
    where
  app X := hσ q
  naturality' X Y f := by
    unfold Hσ
    rw [null_homotopic_map'_comp, comp_null_homotopic_map']
    congr
    ext n m hnm
    simp only [alternating_face_map_complex_map_f, hσ'_naturality]
#align algebraic_topology.dold_kan.nat_trans_Hσ AlgebraicTopology.DoldKan.natTransHσ
-/

#print AlgebraicTopology.DoldKan.map_hσ' /-
/-- The maps `hσ' q n m hnm` are compatible with the application of additive functors. -/
theorem map_hσ' {D : Type _} [Category D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n m : ℕ) (hnm : c.Rel m n) :
    (hσ' q n m hnm : K[((whiskering _ _).obj G).obj X].pt n ⟶ _) =
      G.map (hσ' q n m hnm : K[X].pt n ⟶ _) :=
  by
  unfold hσ' hσ
  split_ifs
  · simp only [functor.map_zero, zero_comp]
  · simpa only [eq_to_hom_map, functor.map_comp, functor.map_zsmul]
#align algebraic_topology.dold_kan.map_hσ' AlgebraicTopology.DoldKan.map_hσ'
-/

#print AlgebraicTopology.DoldKan.map_Hσ /-
/-- The null homotopic maps `Hσ` are compatible with the application of additive functors. -/
theorem map_Hσ {D : Type _} [Category D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n : ℕ) :
    (hσ q : K[((whiskering C D).obj G).obj X] ⟶ _).f n = G.map ((hσ q : K[X] ⟶ _).f n) :=
  by
  unfold Hσ
  have eq := HomologicalComplex.congr_hom (map_null_homotopic_map' G (hσ' q)) n
  simp only [functor.map_homological_complex_map_f, ← map_hσ'] at eq 
  rw [Eq]
  let h := (functor.congr_obj (map_alternating_face_map_complex G) X).symm
  congr
#align algebraic_topology.dold_kan.map_Hσ AlgebraicTopology.DoldKan.map_Hσ
-/

end DoldKan

end AlgebraicTopology

