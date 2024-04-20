/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/
import Algebra.Ring.Idempotents
import RingTheory.Finiteness

#align_import ring_theory.ideal.idempotent_fg from "leanprover-community/mathlib"@"290a7ba01fbcab1b64757bdaa270d28f4dcede35"

/-!
## Lemmas on idempotent finitely generated ideals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Ideal

#print Ideal.isIdempotentElem_iff_of_fg /-
/-- A finitely generated idempotent ideal is generated by an idempotent element -/
theorem isIdempotentElem_iff_of_fg {R : Type _} [CommRing R] (I : Ideal R) (h : I.FG) :
    IsIdempotentElem I ↔ ∃ e : R, IsIdempotentElem e ∧ I = R ∙ e :=
  by
  constructor
  · intro e
    obtain ⟨r, hr, hr'⟩ :=
      Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I I h (by rw [smul_eq_mul]; exact e.ge)
    simp_rw [smul_eq_mul] at hr'
    refine' ⟨r, hr' r hr, antisymm _ ((Submodule.span_singleton_le_iff_mem _ _).mpr hr)⟩
    intro x hx
    rw [← hr' x hx]
    exact ideal.mem_span_singleton'.mpr ⟨_, mul_comm _ _⟩
  · rintro ⟨e, he, rfl⟩
    simp [IsIdempotentElem, Ideal.span_singleton_mul_span_singleton, he.eq]
#align ideal.is_idempotent_elem_iff_of_fg Ideal.isIdempotentElem_iff_of_fg
-/

#print Ideal.isIdempotentElem_iff_eq_bot_or_top /-
theorem isIdempotentElem_iff_eq_bot_or_top {R : Type _} [CommRing R] [IsDomain R] (I : Ideal R)
    (h : I.FG) : IsIdempotentElem I ↔ I = ⊥ ∨ I = ⊤ :=
  by
  constructor
  · intro H
    obtain ⟨e, he, rfl⟩ := (I.is_idempotent_elem_iff_of_fg h).mp H
    simp only [Ideal.submodule_span_eq, Ideal.span_singleton_eq_bot]
    apply or_of_or_of_imp_of_imp (is_idempotent_elem.iff_eq_zero_or_one.mp he) id
    rintro rfl
    simp
  · rintro (rfl | rfl) <;> simp [IsIdempotentElem]
#align ideal.is_idempotent_elem_iff_eq_bot_or_top Ideal.isIdempotentElem_iff_eq_bot_or_top
-/

end Ideal
