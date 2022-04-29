/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.ModelTheory.ElementaryMaps

/-!
# Skolem Functions and Downward Löwenheim–Skolem

## Main Definitions
* `first_order.language.skolem₁` is a language consisting of Skolem functions for another language.

## Main Results
* `first_order.language.exists_small_elementary_substructure` is a weak version of
Downward Löwenheim–Skolem, showing that any `L`-structure admits a small `L`-elementary
substructure.

## TODO
* Bound the cardinality of `L.bounded_formula empty (n + 1)`, and based on that, bound the
cardinality of `(⊥ : (L.sum L.skolem₁).substructure M)` well enough to prove
Downward Löwenheim–Skolem.
* Use `skolem₁` recursively to construct an actual Skolemization of a language.

-/


universe u v w

namespace FirstOrder

namespace Language

open Structure

variable (L : Language.{u, v}) {M : Type w} [Nonempty M] [L.Structure M]

/-- A language consisting of Skolem functions for another language.
Called `skolem₁` because it is the first step in building a Skolemization of a language. -/
def skolem₁ : Language :=
  ⟨fun n => L.BoundedFormula Empty (n + 1), fun _ => Empty⟩

variable {L}

/-- The structure assigning each function symbol of `L.skolem₁` to a skolem function generated with
choice. -/
noncomputable instance skolem₁Structure : L.skolem₁.Structure M :=
  ⟨fun n φ x => Classical.epsilon fun a => φ.realize default (Finₓ.snoc x a : _ → M), fun _ r => Empty.elimₓ r⟩

theorem Substructure.skolem₁_reduct_is_elementary (S : (L.Sum L.skolem₁).Substructure M) :
    (Lhom.sumInl.substructureReduct S).IsElementary := by
  apply (Lhom.sum_inl.substructure_reduct S).is_elementary_of_exists
  intro n φ x a h
  let φ' : (L.sum L.skolem₁).Functions n := Lhom.sum_inr.on_function φ
  exact
    ⟨⟨fun_map φ' (coe ∘ x), S.fun_mem (Lhom.sum_inr.on_function φ) (coe ∘ x) fun i => (x i).2⟩,
      Classical.epsilon_spec ⟨a, h⟩⟩

/-- Any `L.sum L.skolem₁`-substructure is an elementary `L`-substructure. -/
noncomputable def Substructure.elementarySkolem₁Reduct (S : (L.Sum L.skolem₁).Substructure M) :
    L.ElementarySubstructure M :=
  ⟨Lhom.sumInl.substructureReduct S, fun _ => S.skolem₁_reduct_is_elementary⟩

theorem Substructure.coe_sort_elementary_skolem₁_reduct (S : (L.Sum L.skolem₁).Substructure M) :
    (S.elementarySkolem₁Reduct : Type w) = S :=
  rfl

open Cardinal

open Cardinal

variable (L) (M)

instance : Small (⊥ : (L.Sum L.skolem₁).Substructure M).elementarySkolem₁Reduct := by
  rw [substructure.coe_sort_elementary_skolem₁_reduct]
  infer_instance

theorem exists_small_elementary_substructure : ∃ S : L.ElementarySubstructure M, Small.{max u v} S :=
  ⟨Substructure.elementarySkolem₁Reduct ⊥, inferInstance⟩

end Language

end FirstOrder

