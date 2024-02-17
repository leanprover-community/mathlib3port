/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Algebra.Module.Pid
import Data.Zmod.Quotient

#align_import group_theory.finite_abelian from "leanprover-community/mathlib"@"1a51edf13debfcbe223fa06b1cb353b9ed9751cc"

/-!
# Structure of finite(ly generated) abelian groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

* `add_comm_group.equiv_free_prod_direct_sum_zmod` : Any finitely generated abelian group is the
  product of a power of `ℤ` and a direct sum of some `zmod (p i ^ e i)` for some prime powers
  `p i ^ e i`.
* `add_comm_group.equiv_direct_sum_zmod_of_fintype` : Any finite abelian group is a direct sum of
  some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`.

-/


open scoped DirectSum

universe u

namespace Module

variable (M : Type u)

#print Module.finite_of_fg_torsion /-
theorem finite_of_fg_torsion [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]
    (hM : Module.IsTorsion ℤ M) : Finite M :=
  by
  rcases Module.equiv_directSum_of_isTorsion hM with ⟨ι, _, p, h, e, ⟨l⟩⟩
  haveI : ∀ i : ι, NeZero (p i ^ e i).natAbs := fun i =>
    ⟨Int.natAbs_ne_zero_of_ne_zero <| pow_ne_zero (e i) (h i).NeZero⟩
  haveI : ∀ i : ι, _root_.finite <| ℤ ⧸ Submodule.span ℤ {p i ^ e i} := fun i =>
    Finite.of_equiv _ (p i ^ e i).quotientSpanEquivZMod.symm.toEquiv
  haveI : _root_.finite (⨁ i, ℤ ⧸ (Submodule.span ℤ {p i ^ e i} : Submodule ℤ ℤ)) :=
    Finite.of_equiv _ dfinsupp.equiv_fun_on_fintype.symm
  exact Finite.of_equiv _ l.symm.to_equiv
#align module.finite_of_fg_torsion Module.finite_of_fg_torsion
-/

end Module

variable (G : Type u)

namespace AddCommGroup

variable [AddCommGroup G]

#print AddCommGroup.equiv_free_prod_directSum_zmod /-
/-- **Structure theorem of finitely generated abelian groups** : Any finitely generated abelian
group is the product of a power of `ℤ` and a direct sum of some `zmod (p i ^ e i)` for some
prime powers `p i ^ e i`. -/
theorem equiv_free_prod_directSum_zmod [hG : AddGroup.FG G] :
    ∃ (n : ℕ) (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime <| p i) (e : ι → ℕ),
      Nonempty <| G ≃+ (Fin n →₀ ℤ) × ⨁ i : ι, ZMod (p i ^ e i) :=
  by
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ :=
    @Module.equiv_free_prod_directSum _ _ _ _ _ _ _ (module.finite.iff_add_group_fg.mpr hG)
  refine' ⟨n, ι, fι, fun i => (p i).natAbs, fun i => _, e, ⟨_⟩⟩
  · rw [← Int.prime_iff_natAbs_prime, ← irreducible_iff_prime]; exact hp i
  exact
    f.to_add_equiv.trans
      ((AddEquiv.refl _).prodCongr <|
        DFinsupp.mapRange.addEquiv fun i =>
          ((Int.quotientSpanEquivZMod _).trans <|
              ZMod.ringEquivCongr <| (p i).natAbs_pow _).toAddEquiv)
#align add_comm_group.equiv_free_prod_direct_sum_zmod AddCommGroup.equiv_free_prod_directSum_zmod
-/

#print AddCommGroup.equiv_directSum_zmod_of_finite /-
/-- **Structure theorem of finite abelian groups** : Any finite abelian group is a direct sum of
some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`. -/
theorem equiv_directSum_zmod_of_finite [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime <| p i) (e : ι → ℕ),
      Nonempty <| G ≃+ ⨁ i : ι, ZMod (p i ^ e i) :=
  by
  cases nonempty_fintype G
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ := equiv_free_prod_direct_sum_zmod G
  cases n
  · exact ⟨ι, fι, p, hp, e, ⟨f.trans AddEquiv.uniqueProd⟩⟩
  · haveI := @Fintype.prodLeft _ _ _ (Fintype.ofEquiv G f.to_equiv) _
    exact
      (Fintype.ofSurjective (fun f : Fin n.succ →₀ ℤ => f 0) fun a =>
            ⟨Finsupp.single 0 a, Finsupp.single_eq_same⟩).False.elim
#align add_comm_group.equiv_direct_sum_zmod_of_fintype AddCommGroup.equiv_directSum_zmod_of_finite
-/

#print AddCommGroup.finite_of_fg_torsion /-
theorem finite_of_fg_torsion [hG' : AddGroup.FG G] (hG : AddMonoid.IsTorsion G) : Finite G :=
  @Module.finite_of_fg_torsion _ _ _ (Module.Finite.iff_addGroup_fg.mpr hG') <|
    AddMonoid.isTorsion_iff_isTorsion_int.mp hG
#align add_comm_group.finite_of_fg_torsion AddCommGroup.finite_of_fg_torsion
-/

end AddCommGroup

namespace CommGroup

#print CommGroup.finite_of_fg_torsion /-
theorem finite_of_fg_torsion [CommGroup G] [Group.FG G] (hG : Monoid.IsTorsion G) : Finite G :=
  @Finite.of_equiv _ _ (AddCommGroup.finite_of_fg_torsion (Additive G) hG) Multiplicative.ofAdd
#align comm_group.finite_of_fg_torsion CommGroup.finite_of_fg_torsion
-/

end CommGroup

