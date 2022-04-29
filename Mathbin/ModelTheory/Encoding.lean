/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Computability.Encoding
import Mathbin.ModelTheory.Syntax
import Mathbin.SetTheory.Cardinal.Ordinal

/-! # Encodings and Cardinality of First-Order Syntax

## Main Definitions
* Terms can be encoded as lists with `first_order.language.term.list_encode` and
`first_order.language.term.list_decode`.

## Main Results
* `first_order.language.term.card_le` shows that the number of terms in `L.term α` is at most
`# (α ⊕ Σ i, L.functions i) + ω`.

## TODO
* An encoding for formulas
* `primcodable` instances for terms and formulas, based on the `encoding`s
* Computability facts about term and formula operations, to set up a computability approach to
incompleteness

-/


universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

variable {M : Type w} {N P : Type _} [L.Structure M] [L.Structure N] [L.Structure P]

variable {α : Type u'} {β : Type v'}

open FirstOrder Cardinal

open Computability List Structure Cardinal Finₓ

namespace Term

/-- Encodes a term as a list of variables and function symbols. -/
def listEncodeₓ : L.Term α → List (Sum α (Σi, L.Functions i))
  | var i => [Sum.inl i]
  | func f ts => Sum.inr (⟨_, f⟩ : Σi, L.Functions i) :: (List.finRange _).bind fun i => (ts i).listEncode

/-- Decodes a list of variables and function symbols as a list of terms. -/
def listDecodeₓ : List (Sum α (Σi, L.Functions i)) → List (Option (L.Term α))
  | [] => []
  | Sum.inl a :: l => some (var a) :: list_decode l
  | Sum.inr ⟨n, f⟩ :: l =>
    if h : ∀ i : Finₓ n, ((list_decode l).nth i).join.isSome then
      (func f fun i => Option.getₓ (h i)) :: (list_decode l).drop n
    else [none]

theorem list_decode_encode_list (l : List (L.Term α)) : listDecodeₓ (l.bind listEncodeₓ) = l.map Option.some := by
  suffices h :
    ∀ t : L.term α l : List (Sum α (Σi, L.functions i)), list_decode (t.listEncode ++ l) = some t :: list_decode l
  · induction' l with t l lih
    · rfl
      
    · rw [cons_bind, h t (l.bind list_encode), lih, List.map]
      
    
  · intro t
    induction' t with a n f ts ih <;> intro l
    · rw [list_encode, singleton_append, list_decode]
      
    · rw [list_encode, cons_append, list_decode]
      have h :
        list_decode (((fin_range n).bind fun i : Finₓ n => (ts i).listEncode) ++ l) =
          (fin_range n).map (Option.some ∘ ts) ++ list_decode l :=
        by
        induction' fin_range n with i l' l'ih
        · rfl
          
        · rw [cons_bind, append_assoc, ih, map_cons, l'ih, cons_append]
          
      have h' :
        ∀ i,
          (list_decode (((fin_range n).bind fun i : Finₓ n => (ts i).listEncode) ++ l)).nth ↑i = some (some (ts i)) :=
        by
        intro i
        rw [h, nth_append, nth_map]
        · simp only [Option.map_eq_some', Function.comp_app, nth_eq_some]
          refine' ⟨i, ⟨lt_of_lt_of_leₓ i.2 (ge_of_eq (length_fin_range _)), _⟩, rfl⟩
          rw [nth_le_fin_range, Finₓ.eta]
          
        · refine' lt_of_lt_of_leₓ i.2 _
          simp
          
      refine' (dif_pos fun i => Option.is_some_iff_exists.2 ⟨ts i, _⟩).trans _
      · rw [Option.join_eq_some, h']
        
      refine' congr (congr rfl (congr rfl (congr rfl (funext fun i => Option.get_of_memₓ _ _)))) _
      · simp [h']
        
      · rw [h, drop_left']
        rw [length_map, length_fin_range]
        
      
    

/-- An encoding of terms as lists. -/
@[simps]
protected def encoding : Encoding (L.Term α) where
  Γ := Sum α (Σi, L.Functions i)
  encode := listEncodeₓ
  decode := fun l => (listDecodeₓ l).head'.join
  decode_encode := fun t => by
    have h := list_decode_encode_list [t]
    rw [bind_singleton] at h
    simp only [h, Option.join, head', List.map, Option.some_bindₓ, id.def]

theorem list_encode_injective : Function.Injective (listEncodeₓ : L.Term α → List (Sum α (Σi, L.Functions i))) :=
  Term.encoding.encode_injective

theorem card_le : # (L.Term α) ≤ max ω (# (Sum α (Σi, L.Functions i))) :=
  lift_le.1 (trans Term.encoding.card_le_card_list (lift_le.2 (mk_list_le_max _)))

instance [Encodable α] [Encodable (Σi, L.Functions i)] : Encodable (L.Term α) :=
  Encodable.ofLeftInjection listEncodeₓ (fun l => (listDecodeₓ l).head'.join) fun t => by
    rw [← bind_singleton list_encode, list_decode_encode_list]
    simp only [Option.join, head', List.map, Option.some_bindₓ, id.def]

theorem card_le_omega [h1 : Nonempty (Encodable α)] [h2 : L.CountableFunctions] : # (L.Term α) ≤ ω := by
  refine' card_le.trans _
  rw [max_le_iff]
  simp only [le_reflₓ, mk_sum, add_le_omega, lift_le_omega, true_andₓ]
  exact ⟨encodable_iff.1 h1, L.card_functions_le_omega⟩

instance small [Small.{u} α] : Small.{u} (L.Term α) :=
  small_of_injective list_encode_injective

end Term

end Language

end FirstOrder

