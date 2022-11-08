/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathbin.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
import Mathbin.AlgebraicGeometry.SpecCat
import Mathbin.RingTheory.GradedAlgebra.Radical

/-!
# Proj as a scheme

This file is to prove that `Proj` is a scheme.

## Notation

* `Proj`      : `Proj` as a locally ringed space
* `Proj.T`    : the underlying topological space of `Proj`
* `Proj| U`   : `Proj` restricted to some open set `U`
* `Proj.T| U` : the underlying topological space of `Proj` restricted to open set `U`
* `pbo f`     : basic open set at `f` in `Proj`
* `Spec`      : `Spec` as a locally ringed space
* `Spec.T`    : the underlying topological space of `Spec`
* `sbo g`     : basic open set at `g` in `Spec`
* `A⁰_x`      : the degree zero part of localized ring `Aₓ`

## Implementation

In `src/algebraic_geometry/projective_spectrum/structure_sheaf.lean`, we have given `Proj` a
structure sheaf so that `Proj` is a locally ringed space. In this file we will prove that `Proj`
equipped with this structure sheaf is a scheme. We achieve this by using an affine cover by basic
open sets in `Proj`, more specifically:

1. We prove that `Proj` can be covered by basic open sets at homogeneous element of positive degree.
2. We prove that for any homogeneous element `f : A` of positive degree `m`, `Proj.T | (pbo f)` is
    homeomorphic to `Spec.T A⁰_f`:
  - forward direction `to_Spec`:
    for any `x : pbo f`, i.e. a relevant homogeneous prime ideal `x`, send it to
    `A⁰_f ∩ span {g / 1 | g ∈ x}` (see `Proj_iso_Spec_Top_component.to_Spec.carrier`). This ideal is
    prime, the proof is in `Proj_iso_Spec_Top_component.to_Spec.to_fun`. The fact that this function
    is continuous is found in `Proj_iso_Spec_Top_component.to_Spec`
  - backward direction `from_Spec`:
    for any `q : Spec A⁰_f`, we send it to `{a | ∀ i, aᵢᵐ/fⁱ ∈ q}`; we need this to be a
    homogeneous prime ideal that is relevant.
    * This is in fact an ideal, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal`;
    * This ideal is also homogeneous, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal.homogeneous`;
    * This ideal is relevant, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.relevant`;
    * This ideal is prime, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.prime`.
    Hence we have a well defined function `Spec.T A⁰_f → Proj.T | (pbo f)`, this function is called
    `Proj_iso_Spec_Top_component.from_Spec.to_fun`. But to prove the continuity of this function,
    we need to prove `from_Spec ∘ to_Spec` and `to_Spec ∘ from_Spec` are both identities (TBC).

## Main Definitions and Statements

* `degree_zero_part`: the degree zero part of the localized ring `Aₓ` where `x` is a homogeneous
  element of degree `n` is the subring of elements of the form `a/f^m` where `a` has degree `mn`.

For a homogeneous element `f` of degree `n`
* `Proj_iso_Spec_Top_component.to_Spec`: `forward f` is the
  continuous map between `Proj.T| pbo f` and `Spec.T A⁰_f`
* `Proj_iso_Spec_Top_component.to_Spec.preimage_eq`: for any `a: A`, if `a/f^m` has degree zero,
  then the preimage of `sbo a/f^m` under `to_Spec f` is `pbo f ∩ pbo a`.

* [Robin Hartshorne, *Algebraic Geometry*][Har77]: Chapter II.2 Proposition 2.5
-/


noncomputable section

namespace AlgebraicGeometry

open DirectSum BigOperators Pointwise BigOperators

open DirectSum SetLike.GradedMonoid Localization

open Finset hiding mk_zero

variable {R A : Type _}

variable [CommRing R] [CommRing A] [Algebra R A]

variable (𝒜 : ℕ → Submodule R A)

variable [GradedAlgebra 𝒜]

open TopCat TopologicalSpace

open CategoryTheory Opposite

open ProjectiveSpectrum.StructureSheaf

-- mathport name: exprProj
local notation "Proj" => ProjCat.toLocallyRingedSpace 𝒜

-- mathport name: «exprProj.T»
-- `Proj` as a locally ringed space
local notation "Proj.T" => Proj.1.1.1

-- mathport name: «exprProj| »
-- the underlying topological space of `Proj`
local notation "Proj| " U => Proj.restrict (Opens.open_embedding (U : Opens Proj.T))

-- mathport name: «exprProj.T| »
-- `Proj` restrict to some open set
local notation "Proj.T| " U =>
  (Proj.restrict (Opens.open_embedding (U : Opens Proj.T))).toSheafedSpace.toPresheafedSpace.1

-- mathport name: «exprpbo »
-- the underlying topological space of `Proj` restricted to some open set
local notation "pbo " x => ProjectiveSpectrum.basicOpen 𝒜 x

-- mathport name: «exprsbo »
-- basic open sets in `Proj`
local notation "sbo " f => PrimeSpectrum.basicOpen f

-- mathport name: «exprSpec »
-- basic open sets in `Spec`
local notation "Spec " ring => SpecCat.locallyRingedSpaceObj (CommRingCat.of Ring)

-- mathport name: «exprSpec.T »
-- `Spec` as a locally ringed space
local notation "Spec.T " ring =>
  (SpecCat.locallyRingedSpaceObj (CommRingCat.of Ring)).toSheafedSpace.toPresheafedSpace.1

-- mathport name: «exprA⁰_ »
-- the underlying topological space of `Spec`
local notation "A⁰_ " f => HomogeneousLocalization.Away 𝒜 f

namespace ProjIsoSpecTopComponent

/-
This section is to construct the homeomorphism between `Proj` restricted at basic open set at
a homogeneous element `x` and `Spec A⁰ₓ` where `A⁰ₓ` is the degree zero part of the localized
ring `Aₓ`.
-/
namespace ToSpec

open Ideal

-- This section is to construct the forward direction :
-- So for any `x` in `Proj| (pbo f)`, we need some point in `Spec A⁰_f`, i.e. a prime ideal,
-- and we need this correspondence to be continuous in their Zariski topology.
variable {𝒜} {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x : Proj| pbo f)

/-- For any `x` in `Proj| (pbo f)`, the corresponding ideal in `Spec A⁰_f`. This fact that this ideal
is prime is proven in `Top_component.forward.to_fun`-/
def carrier : Ideal (A⁰_ f) :=
  Ideal.comap (algebraMap (A⁰_ f) (Away f)) (Ideal.span <| algebraMap A (Away f) '' x.val.asHomogeneousIdeal)

theorem mem_carrier_iff (z : A⁰_ f) :
    z ∈ carrier 𝒜 x ↔ z.val ∈ Ideal.span (algebraMap A (Away f) '' x.1.asHomogeneousIdeal) :=
  Iff.rfl

theorem MemCarrier.clear_denominator' [DecidableEq (Away f)] {z : Localization.Away f}
    (hz : z ∈ span (algebraMap A (Away f) '' x.val.asHomogeneousIdeal)) :
    ∃ (c : algebraMap A (Away f) '' x.1.asHomogeneousIdeal →₀ Away f)(N : ℕ)(acd : ∀ y ∈ c.Support.Image c, A),
      f ^ N • z =
        algebraMap A (Away f)
          (∑ i in c.Support.attach, acd (c i) (Finset.mem_image.mpr ⟨i, ⟨i.2, rfl⟩⟩) * i.1.2.some) :=
  by
  rw [← submodule_span_eq, Finsupp.span_eq_range_total, LinearMap.mem_range] at hz
  rcases hz with ⟨c, eq1⟩
  rw [Finsupp.total_apply, Finsupp.sum] at eq1
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := IsLocalization.exist_integer_multiples_of_finset (Submonoid.powers f) (c.support.image c)
  choose acd hacd using hN
  refine' ⟨c, N, acd, _⟩
  rw [← eq1, smul_sum, map_sum, ← sum_attach]
  congr 1
  ext i
  rw [_root_.map_mul, hacd, (Classical.choose_spec i.1.2).2, smul_eq_mul, smul_mul_assoc]
  rfl

theorem MemCarrier.clear_denominator [DecidableEq (Away f)] {z : A⁰_ f} (hz : z ∈ carrier 𝒜 x) :
    ∃ (c : algebraMap A (Away f) '' x.1.asHomogeneousIdeal →₀ Away f)(N : ℕ)(acd : ∀ y ∈ c.Support.Image c, A),
      f ^ N • z.val =
        algebraMap A (Away f)
          (∑ i in c.Support.attach, acd (c i) (Finset.mem_image.mpr ⟨i, ⟨i.2, rfl⟩⟩) * i.1.2.some) :=
  MemCarrier.clear_denominator' x <| (mem_carrier_iff 𝒜 x z).mpr hz

theorem disjoint : Disjoint (x.1.asHomogeneousIdeal.toIdeal : Set A) (Submonoid.powers f : Set A) := by
  by_contra rid
  rw [Set.not_disjoint_iff] at rid
  choose g hg using rid
  obtain ⟨hg1, ⟨k, rfl⟩⟩ := hg
  by_cases k_ineq:0 < k
  · erw [x.1.IsPrime.pow_mem_iff_mem _ k_ineq] at hg1
    exact x.2 hg1
    
  · erw [show k = 0 by linarith, pow_zero, ← Ideal.eq_top_iff_one] at hg1
    apply x.1.IsPrime.1
    exact hg1
    

theorem carrier_ne_top : carrier 𝒜 x ≠ ⊤ := by
  have eq_top := Disjoint x
  classical
  contrapose! eq_top
  obtain ⟨c, N, acd, eq1⟩ := mem_carrier.clear_denominator _ x ((Ideal.eq_top_iff_one _).mp eq_top)
  rw [Algebra.smul_def, HomogeneousLocalization.one_val, mul_one] at eq1
  change Localization.mk (f ^ N) 1 = mk (∑ _, _) 1 at eq1
  simp only [mk_eq_mk', IsLocalization.eq] at eq1
  rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩
  erw [mul_one, mul_one] at eq1
  change f ^ _ * f ^ _ = _ * f ^ _ at eq1
  rw [Set.not_disjoint_iff_nonempty_inter]
  refine'
    ⟨f ^ N * f ^ M, eq1.symm ▸ mul_mem_right _ _ (sum_mem _ fun i hi => mul_mem_left _ _ _), ⟨N + M, by rw [pow_add]⟩⟩
  generalize_proofs h
  exact (Classical.choose_spec h).1

variable (f)

/-- The function between the basic open set `D(f)` in `Proj` to the corresponding basic open set in
`Spec A⁰_f`. This is bundled into a continuous map in `Top_component.forward`.
-/
def toFun (x : Proj.T| pbo f) : Spec.T A⁰_ f :=
  ⟨carrier 𝒜 x, carrier_ne_top x, fun x1 x2 hx12 => by
    classical
    simp only [mem_carrier_iff] at hx12⊢
    let J := span (⇑(algebraMap A (away f)) '' x.val.as_homogeneous_ideal)
    suffices h : ∀ x y : Localization.Away f, x * y ∈ J → x ∈ J ∨ y ∈ J
    · rw [HomogeneousLocalization.mul_val] at hx12
      exact h x1.val x2.val hx12
      
    clear x1 x2 hx12
    intro x1 x2 hx12
    induction' x1 using Localization.induction_on with data_x1
    induction' x2 using Localization.induction_on with data_x2
    rcases data_x1, data_x2 with ⟨⟨a1, _, ⟨n1, rfl⟩⟩, ⟨a2, _, ⟨n2, rfl⟩⟩⟩
    rcases mem_carrier.clear_denominator' x hx12 with ⟨c, N, acd, eq1⟩
    simp only [Algebra.smul_def] at eq1
    change Localization.mk (f ^ N) 1 * (mk _ _ * mk _ _) = mk (∑ _, _) _ at eq1
    simp only [Localization.mk_mul, one_mul] at eq1
    simp only [mk_eq_mk', IsLocalization.eq] at eq1
    rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩
    rw [Submonoid.coe_one, mul_one] at eq1
    change _ * _ * f ^ _ = _ * (f ^ _ * f ^ _) * f ^ _ at eq1
    rcases x.1.IsPrime.mem_or_mem (show a1 * a2 * f ^ N * f ^ M ∈ _ from _) with (h1 | rid2)
    rcases x.1.IsPrime.mem_or_mem h1 with (h1 | rid1)
    rcases x.1.IsPrime.mem_or_mem h1 with (h1 | h2)
    · left
      simp only [show (mk a1 ⟨f ^ n1, _⟩ : away f) = mk a1 1 * mk 1 ⟨f ^ n1, ⟨n1, rfl⟩⟩ by
          rw [Localization.mk_mul, mul_one, one_mul]]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, h1, rfl⟩)
      
    · right
      simp only [show (mk a2 ⟨f ^ n2, _⟩ : away f) = mk a2 1 * mk 1 ⟨f ^ n2, ⟨n2, rfl⟩⟩ by
          rw [Localization.mk_mul, mul_one, one_mul]]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, h2, rfl⟩)
      
    · exact False.elim (x.2 (x.1.IsPrime.mem_of_pow_mem N rid1))
      
    · exact False.elim (x.2 (x.1.IsPrime.mem_of_pow_mem M rid2))
      
    · rw [mul_comm _ (f ^ N), eq1]
      refine' mul_mem_right _ _ (mul_mem_right _ _ (sum_mem _ fun i hi => mul_mem_left _ _ _))
      generalize_proofs h
      exact (Classical.choose_spec h).1
      ⟩

/-
The preimage of basic open set `D(a/f^n)` in `Spec A⁰_f` under the forward map from `Proj A` to
`Spec A⁰_f` is the basic open set `D(a) ∩ D(f)` in  `Proj A`. This lemma is used to prove that the
forward map is continuous.
-/
theorem preimage_eq (a b : A) (k : ℕ) (a_mem : a ∈ 𝒜 k) (b_mem1 : b ∈ 𝒜 k) (b_mem2 : b ∈ Submonoid.powers f) :
    toFun 𝒜 f ⁻¹'
        (@PrimeSpectrum.basicOpen (A⁰_ f) _ (Quotient.mk' ⟨k, ⟨a, a_mem⟩, ⟨b, b_mem1⟩, b_mem2⟩) :
          Set (PrimeSpectrum (HomogeneousLocalization.Away 𝒜 f))) =
      { x | x.1 ∈ (pbo f) ⊓ pbo a } :=
  by
  classical
  ext1 y
  constructor <;> intro hy
  · refine' ⟨y.2, _⟩
    rw [Set.mem_preimage, opens.mem_coe, PrimeSpectrum.mem_basic_open] at hy
    rw [ProjectiveSpectrum.mem_coe_basic_open]
    intro a_mem_y
    apply hy
    rw [to_fun, mem_carrier_iff, HomogeneousLocalization.val_mk', Subtype.coe_mk]
    dsimp
    rcases b_mem2 with ⟨k, hk⟩
    simp only [show (mk a ⟨b, ⟨k, hk⟩⟩ : away f) = mk 1 ⟨f ^ k, ⟨_, rfl⟩⟩ * mk a 1 by
        rw [mk_mul, one_mul, mul_one]
        congr
        rw [hk]]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, a_mem_y, rfl⟩)
    
  · change y.1 ∈ _ at hy
    rcases hy with ⟨hy1, hy2⟩
    rw [ProjectiveSpectrum.mem_coe_basic_open] at hy1 hy2
    rw [Set.mem_preimage, to_fun, opens.mem_coe, PrimeSpectrum.mem_basic_open]
    intro rid
    dsimp at rid
    rcases mem_carrier.clear_denominator 𝒜 _ rid with ⟨c, N, acd, eq1⟩
    rw [Algebra.smul_def] at eq1
    change Localization.mk (f ^ N) 1 * mk _ _ = mk (∑ _, _) _ at eq1
    rw [mk_mul, one_mul, mk_eq_mk', IsLocalization.eq] at eq1
    rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩
    rw [Submonoid.coe_one, mul_one] at eq1
    simp only [Subtype.coe_mk] at eq1
    rcases y.1.IsPrime.mem_or_mem (show a * f ^ N * f ^ M ∈ _ from _) with (H1 | H3)
    rcases y.1.IsPrime.mem_or_mem H1 with (H1 | H2)
    · exact hy2 H1
      
    · exact y.2 (y.1.IsPrime.mem_of_pow_mem N H2)
      
    · exact y.2 (y.1.IsPrime.mem_of_pow_mem M H3)
      
    · rw [mul_comm _ (f ^ N), eq1]
      refine' mul_mem_right _ _ (mul_mem_right _ _ (sum_mem _ fun i hi => mul_mem_left _ _ _))
      generalize_proofs h
      exact (Classical.choose_spec h).1
      
    

end ToSpec

section

variable {𝒜}

/-- The continuous function between the basic open set `D(f)` in `Proj` to the corresponding basic
open set in `Spec A⁰_f`.
-/
def toSpec {f : A} : (Proj.T| pbo f) ⟶ Spec.T A⁰_ f where
  toFun := ToSpec.toFun 𝒜 f
  continuous_to_fun := by
    apply is_topological_basis.continuous PrimeSpectrum.is_topological_basis_basic_opens
    rintro _ ⟨⟨k, ⟨a, ha⟩, ⟨b, hb1⟩, ⟨k', hb2⟩⟩, rfl⟩
    dsimp
    erw [to_Spec.preimage_eq f a b k ha hb1 ⟨k', hb2⟩]
    refine' is_open_induced_iff.mpr ⟨(pbo f).1 ⊓ (pbo a).1, IsOpen.inter (pbo f).2 (pbo a).2, _⟩
    ext z
    constructor <;> intro hz <;> simpa [Set.mem_preimage]

end

namespace FromSpec

open GradedAlgebra SetLike

open Finset hiding mk_zero

open _Root_.HomogeneousLocalization

variable {𝒜} {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m)

/- ./././Mathport/Syntax/Translate/Expr.lean:332:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:332:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def mem_tac : tactic Unit :=
  let b : tactic Unit := sorry
  b <|> sorry

include f_deg

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.233200865.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.233200865.mem_tac -/
/-- The function from `Spec A⁰_f` to `Proj|D(f)` is defined by `q ↦ {a | aᵢᵐ/fⁱ ∈ q}`, i.e. sending
`q` a prime ideal in `A⁰_f` to the homogeneous prime relevant ideal containing only and all the
elements `a : A` such that for every `i`, the degree 0 element formed by dividing the `m`-th power
of the `i`-th projection of `a` by the `i`-th power of the degree-`m` homogeneous element `f`,
lies in `q`.

The set `{a | aᵢᵐ/fⁱ ∈ q}`
* is an ideal, as proved in `carrier.as_ideal`;
* is homogeneous, as proved in `carrier.as_homogeneous_ideal`;
* is prime, as proved in `carrier.as_ideal.prime`;
* is relevant, as proved in `carrier.relevant`.
-/
def Carrier (q : Spec.T A⁰_ f) : Set A :=
  { a |
    ∀ i,
      (Quotient.mk'
          ⟨m * i,
            ⟨proj 𝒜 i a ^ m, by
              run_tac
                mem_tac⟩,
            ⟨f ^ i, by
              rw [mul_comm] <;>
                run_tac
                  mem_tac⟩,
            ⟨_, rfl⟩⟩ :
          A⁰_ f) ∈
        q.1 }

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.233200865.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.233200865.mem_tac -/
theorem mem_carrier_iff (q : Spec.T A⁰_ f) (a : A) :
    a ∈ Carrier f_deg q ↔
      ∀ i,
        (Quotient.mk'
            ⟨m * i,
              ⟨proj 𝒜 i a ^ m, by
                run_tac
                  mem_tac⟩,
              ⟨f ^ i, by
                rw [mul_comm] <;>
                  run_tac
                    mem_tac⟩,
              ⟨_, rfl⟩⟩ :
            A⁰_ f) ∈
          q.1 :=
  Iff.rfl

theorem mem_carrier_iff' (q : Spec.T A⁰_ f) (a : A) :
    a ∈ Carrier f_deg q ↔
      ∀ i,
        (Localization.mk (proj 𝒜 i a ^ m) ⟨f ^ i, ⟨i, rfl⟩⟩ : Localization.Away f) ∈
          algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) '' q.1.1 :=
  (mem_carrier_iff f_deg q a).trans
    (by
      constructor <;> intro h i <;> specialize h i
      · rw [Set.mem_image]
        refine' ⟨_, h, rfl⟩
        
      · rw [Set.mem_image] at h
        rcases h with ⟨x, h, hx⟩
        convert h
        rw [ext_iff_val, val_mk']
        dsimp only [Subtype.coe_mk]
        rw [← hx]
        rfl
        )

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.233200865.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.233200865.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.233200865.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.233200865.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.233200865.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.233200865.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.233200865.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.233200865.mem_tac -/
theorem Carrier.add_mem (q : Spec.T A⁰_ f) {a b : A} (ha : a ∈ Carrier f_deg q) (hb : b ∈ Carrier f_deg q) :
    a + b ∈ Carrier f_deg q := by
  refine' fun i => (q.2.mem_or_mem _).elim id id
  change (Quotient.mk' ⟨_, _, _, _⟩ : A⁰_ f) ∈ q.1
  dsimp only [Subtype.coe_mk]
  simp_rw [← pow_add, map_add, add_pow, mul_comm, ← nsmul_eq_mul]
  let g : ℕ → A⁰_ f := fun j =>
    (m + m).choose j •
      if h2 : m + m < j then 0
      else
        if h1 : j ≤ m then
          Quotient.mk'
              ⟨m * i, ⟨proj 𝒜 i a ^ j * proj 𝒜 i b ^ (m - j), _⟩,
                ⟨_, by
                  rw [mul_comm] <;>
                    run_tac
                      mem_tac⟩,
                ⟨i, rfl⟩⟩ *
            Quotient.mk'
              ⟨m * i,
                ⟨proj 𝒜 i b ^ m, by
                  run_tac
                    mem_tac⟩,
                ⟨_, by
                  rw [mul_comm] <;>
                    run_tac
                      mem_tac⟩,
                ⟨i, rfl⟩⟩
        else
          Quotient.mk'
              ⟨m * i,
                ⟨proj 𝒜 i a ^ m, by
                  run_tac
                    mem_tac⟩,
                ⟨_, by
                  rw [mul_comm] <;>
                    run_tac
                      mem_tac⟩,
                ⟨i, rfl⟩⟩ *
            Quotient.mk'
              ⟨m * i, ⟨proj 𝒜 i a ^ (j - m) * proj 𝒜 i b ^ (m + m - j), _⟩,
                ⟨_, by
                  rw [mul_comm] <;>
                    run_tac
                      mem_tac⟩,
                ⟨i, rfl⟩⟩
  rotate_left
  · rw [(_ : m * i = _)]
    run_tac
      mem_tac
    rw [← add_smul, Nat.add_sub_of_le h1]
    rfl
    
  · rw [(_ : m * i = _)]
    run_tac
      mem_tac
    rw [← add_smul]
    congr
    zify [le_of_not_lt h2, le_of_not_le h1]
    abel
    
  convert_to (∑ i in range (m + m + 1), g i) ∈ q.1
  swap
  · refine' q.1.sum_mem fun j hj => nsmul_mem _ _
    split_ifs
    exacts[q.1.zero_mem, q.1.mul_mem_left _ (hb i), q.1.mul_mem_right _ (ha i)]
    
  rw [ext_iff_val, val_mk']
  change _ = (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f)) _
  dsimp only [Subtype.coe_mk]
  rw [map_sum, mk_sum]
  apply Finset.sum_congr rfl fun j hj => _
  change _ = HomogeneousLocalization.val _
  rw [HomogeneousLocalization.smul_val]
  split_ifs with h2 h1
  · exact ((Finset.mem_range.1 hj).not_le h2).elim
    
  all_goals
  simp only [mul_val, zero_val, val_mk', Subtype.coe_mk, mk_mul, ← smul_mk]
  congr 2
  · rw [mul_assoc, ← pow_add, add_comm (m - j), Nat.add_sub_assoc h1]
    
  · simp_rw [pow_add]
    rfl
    
  · rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (le_of_not_le h1)]
    
  · simp_rw [pow_add]
    rfl
    

variable (hm : 0 < m) (q : Spec.T A⁰_ f)

include hm

theorem Carrier.zero_mem : (0 : A) ∈ Carrier f_deg q := fun i => by
  convert Submodule.zero_mem q.1 using 1
  rw [ext_iff_val, val_mk', zero_val]
  simp_rw [map_zero, zero_pow hm]
  convert Localization.mk_zero _ using 1

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.233200865.mem_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.233200865.mem_tac -/
theorem Carrier.smul_mem (c x : A) (hx : x ∈ Carrier f_deg q) : c • x ∈ Carrier f_deg q := by
  revert c
  refine' DirectSum.Decomposition.induction_on 𝒜 _ _ _
  · rw [zero_smul]
    exact carrier.zero_mem f_deg hm _
    
  · rintro n ⟨a, ha⟩ i
    simp_rw [Subtype.coe_mk, proj_apply, smul_eq_mul, coe_decompose_mul_of_left_mem 𝒜 i ha]
    split_ifs
    · convert_to
        (Quotient.mk' ⟨_, ⟨a ^ m, pow_mem_graded m ha⟩, ⟨_, _⟩, ⟨n, rfl⟩⟩ *
            Quotient.mk'
              ⟨_,
                ⟨proj 𝒜 (i - n) x ^ m, by
                  run_tac
                    mem_tac⟩,
                ⟨_, _⟩, ⟨i - n, rfl⟩⟩ :
            A⁰_ f) ∈
          q.1
      · erw [ext_iff_val, val_mk', mul_val, val_mk', val_mk', Subtype.coe_mk]
        simp_rw [mul_pow, Subtype.coe_mk]
        rw [Localization.mk_mul]
        congr
        erw [← pow_add, Nat.add_sub_of_le h]
        
      · exact Ideal.mul_mem_left _ _ (hx _)
        rw [smul_eq_mul, mul_comm]
        run_tac
          mem_tac
        
      
    · simp_rw [zero_pow hm]
      convert carrier.zero_mem f_deg hm q i
      rw [map_zero, zero_pow hm]
      
    
  · simp_rw [add_smul]
    exact fun _ _ => carrier.add_mem f_deg q
    

/-- For a prime ideal `q` in `A⁰_f`, the set `{a | aᵢᵐ/fⁱ ∈ q}` as an ideal.
-/
def Carrier.asIdeal : Ideal A where
  Carrier := Carrier f_deg q
  zero_mem' := Carrier.zero_mem f_deg hm q
  add_mem' a b := Carrier.add_mem f_deg q
  smul_mem' := Carrier.smul_mem f_deg hm q

theorem Carrier.asIdeal.homogeneous : (Carrier.asIdeal f_deg hm q).IsHomogeneous 𝒜 := fun i a ha j =>
  (em (i = j)).elim (fun h => h ▸ by simpa only [proj_apply, decompose_coe, of_eq_same] using ha _) fun h => by
    simp only [proj_apply, decompose_of_mem_ne 𝒜 (Submodule.coe_mem (decompose 𝒜 a i)) h, zero_pow hm]
    convert carrier.zero_mem f_deg hm q j
    rw [map_zero, zero_pow hm]

/-- For a prime ideal `q` in `A⁰_f`, the set `{a | aᵢᵐ/fⁱ ∈ q}` as a homogeneous ideal.
-/
def Carrier.asHomogeneousIdeal : HomogeneousIdeal 𝒜 :=
  ⟨Carrier.asIdeal f_deg hm q, Carrier.asIdeal.homogeneous f_deg hm q⟩

theorem Carrier.denom_not_mem : f ∉ Carrier.asIdeal f_deg hm q := fun rid =>
  q.IsPrime.ne_top <|
    (Ideal.eq_top_iff_one _).mpr
      (by
        convert rid m
        simpa only [ext_iff_val, one_val, proj_apply, decompose_of_mem_same _ f_deg, val_mk'] using
          (mk_self (⟨_, m, rfl⟩ : Submonoid.powers f)).symm)

theorem Carrier.relevant : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ Carrier.asHomogeneousIdeal f_deg hm q := fun rid =>
  Carrier.denom_not_mem f_deg hm q <| rid <| DirectSum.decompose_of_mem_ne 𝒜 f_deg hm.ne'

theorem Carrier.asIdeal.ne_top : Carrier.asIdeal f_deg hm q ≠ ⊤ := fun rid =>
  Carrier.denom_not_mem f_deg hm q (rid.symm ▸ Submodule.mem_top)

theorem Carrier.asIdeal.prime : (Carrier.asIdeal f_deg hm q).IsPrime :=
  ((Carrier.asIdeal.homogeneous f_deg hm q).is_prime_of_homogeneous_mem_or_mem (Carrier.asIdeal.ne_top f_deg hm q))
    fun x y ⟨nx, hnx⟩ ⟨ny, hny⟩ hxy =>
    show (∀ i, _ ∈ _) ∨ ∀ i, _ ∈ _ by
      rw [← and_forall_ne nx, and_iff_left, ← and_forall_ne ny, and_iff_left]
      · apply q.2.mem_or_mem
        convert hxy (nx + ny) using 1
        simp_rw [proj_apply, decompose_of_mem_same 𝒜 hnx, decompose_of_mem_same 𝒜 hny,
          decompose_of_mem_same 𝒜 (mul_mem hnx hny), mul_pow, pow_add]
        simpa only [ext_iff_val, val_mk', mul_val, mk_mul]
        
      all_goals
      intro n hn
      convert q.1.zero_mem using 1
      rw [ext_iff_val, val_mk', zero_val]
      simp_rw [proj_apply, Subtype.coe_mk]
      convert mk_zero _
      rw [decompose_of_mem_ne 𝒜 _ hn.symm, zero_pow hm]
      · first |exact hnx|exact hny
        

variable (f_deg)

/-- The function `Spec A⁰_f → Proj|D(f)` by sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}`.
-/
def toFun : (Spec.T A⁰_ f) → Proj.T| pbo f := fun q =>
  ⟨⟨Carrier.asHomogeneousIdeal f_deg hm q, Carrier.asIdeal.prime f_deg hm q, Carrier.relevant f_deg hm q⟩,
    (ProjectiveSpectrum.mem_basic_open _ f _).mp <| Carrier.denom_not_mem f_deg hm q⟩

end FromSpec

end ProjIsoSpecTopComponent

end AlgebraicGeometry

