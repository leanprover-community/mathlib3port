import Mathbin.Algebra.Periodic
import Mathbin.Data.Nat.Count
import Mathbin.Data.Nat.Interval

/-!
# Periodic Functions on ℕ

This file identifies a few functions on `ℕ` which are periodic, and also proves a lemma about
periodic predicates which helps determine their cardinality when filtering intervals over them.
-/


namespace Nat

open Nat Function

theorem periodic_gcd (a : ℕ) : periodic (gcd a) a := by
  simp only [forall_const, gcd_add_self_right, eq_self_iff_true, periodic]

theorem periodic_coprime (a : ℕ) : periodic (coprime a) a := by
  simp only [coprime_add_self_right, forall_const, iff_selfₓ, eq_iff_iff, periodic]

theorem periodic_mod (a : ℕ) : periodic (fun n => n % a) a := by
  simp only [forall_const, eq_self_iff_true, add_mod_right, periodic]

theorem _root_.function.periodic.map_mod_nat {α : Type _} {f : ℕ → α} {a : ℕ} (hf : periodic f a) :
    ∀ n, f (n % a) = f n := fun n => by
  conv_rhs => rw [← Nat.mod_add_divₓ n a, mul_comm, ← nsmul_eq_mul, hf.nsmul]

section Multiset

open Multiset

/-- An interval of length `a` filtered over a periodic predicate of period `a` has cardinality
equal to the number naturals below `a` for which `p a` is true. -/
theorem filter_multiset_Ico_card_eq_of_periodic (n a : ℕ) (p : ℕ → Prop) [DecidablePred p] (pp : periodic p a) :
    (filter p (Ico n (n + a))).card = a.count p := by
  rw [count_eq_card_filter_range, Finset.card, Finset.filter_val, Finset.range_coe, ← multiset_Ico_map_mod n, ←
    map_count_true_eq_filter_card, ← map_count_true_eq_filter_card, map_map, Function.comp]
  simp only [pp.map_mod_nat]

end Multiset

section Finset

open Finset

/-- An interval of length `a` filtered over a periodic predicate of period `a` has cardinality
equal to the number naturals below `a` for which `p a` is true. -/
theorem filter_Ico_card_eq_of_periodic (n a : ℕ) (p : ℕ → Prop) [DecidablePred p] (pp : periodic p a) :
    ((Ico n (n + a)).filter p).card = a.count p :=
  filter_multiset_Ico_card_eq_of_periodic n a p pp

end Finset

end Nat

