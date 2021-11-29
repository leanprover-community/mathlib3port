import Mathbin.Algebra.Associated 
import Mathbin.Algebra.BigOperators.Basic

/-!
# Prime elements in rings
This file contains lemmas about prime elements of commutative rings.
-/


section CommCancelMonoidWithZero

variable {R : Type _} [CommCancelMonoidWithZero R]

open Finset

open_locale BigOperators

-- error in RingTheory.Prime: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `x * y = a * ∏ i in s, p i` where `p i` is always prime, then
  `x` and `y` can both be written as a divisor of `a` multiplied by
  a product over a subset of `s`  -/
theorem mul_eq_mul_prime_prod
{α : Type*}
[decidable_eq α]
{x y a : R}
{s : finset α}
{p : α → R}
(hp : ∀ i «expr ∈ » s, prime (p i))
(hx : «expr = »(«expr * »(x, y), «expr * »(a, «expr∏ in , »((i), s, p i)))) : «expr∃ , »((t u : finset α)
 (b
  c : R), «expr ∧ »(«expr = »(«expr ∪ »(t, u), s), «expr ∧ »(disjoint t u, «expr ∧ »(«expr = »(a, «expr * »(b, c)), «expr ∧ »(«expr = »(x, «expr * »(b, «expr∏ in , »((i), t, p i))), «expr = »(y, «expr * »(c, «expr∏ in , »((i), u, p i)))))))) :=
begin
  induction [expr s] ["using", ident finset.induction] ["with", ident i, ident s, ident his, ident ih] ["generalizing", ident x, ident y, ident a],
  { exact [expr ⟨«expr∅»(), «expr∅»(), x, y, by simp [] [] [] ["[", expr hx, "]"] [] []⟩] },
  { rw ["[", expr prod_insert his, ",", "<-", expr mul_assoc, "]"] ["at", ident hx],
    have [ident hpi] [":", expr prime (p i)] [],
    { exact [expr hp i (mem_insert_self _ _)] },
    rcases [expr ih (λ
      i
      hi, hp i (mem_insert_of_mem hi)) hx, "with", "⟨", ident t, ",", ident u, ",", ident b, ",", ident c, ",", ident htus, ",", ident htu, ",", ident hbc, ",", ident rfl, ",", ident rfl, "⟩"],
    have [ident hit] [":", expr «expr ∉ »(i, t)] [],
    from [expr λ hit, his «expr ▸ »(htus, mem_union_left _ hit)],
    have [ident hiu] [":", expr «expr ∉ »(i, u)] [],
    from [expr λ hiu, his «expr ▸ »(htus, mem_union_right _ hiu)],
    obtain ["⟨", ident d, ",", ident rfl, "⟩", "|", "⟨", ident d, ",", ident rfl, "⟩", ":", expr «expr ∨ »(«expr ∣ »(p i, b), «expr ∣ »(p i, c))],
    from [expr hpi.dvd_or_dvd ⟨a, by rw ["[", "<-", expr hbc, ",", expr mul_comm, "]"] []⟩],
    { rw ["[", expr mul_assoc, ",", expr mul_comm a, ",", expr mul_right_inj' hpi.ne_zero, "]"] ["at", ident hbc],
      exact [expr ⟨insert i t, u, d, c, by rw ["[", expr insert_union, ",", expr htus, "]"] [], disjoint_insert_left.2 ⟨hiu, htu⟩, by simp [] [] [] ["[", expr hbc, ",", expr prod_insert hit, ",", expr mul_assoc, ",", expr mul_comm, ",", expr mul_left_comm, "]"] [] []⟩] },
    { rw ["[", "<-", expr mul_assoc, ",", expr mul_right_comm b, ",", expr mul_left_inj' hpi.ne_zero, "]"] ["at", ident hbc],
      exact [expr ⟨t, insert i u, b, d, by rw ["[", expr union_insert, ",", expr htus, "]"] [], disjoint_insert_right.2 ⟨hit, htu⟩, by simp [] [] [] ["[", "<-", expr hbc, ",", expr prod_insert hiu, ",", expr mul_assoc, ",", expr mul_comm, ",", expr mul_left_comm, "]"] [] []⟩] } }
end

/-- If ` x * y = a * p ^ n` where `p` is prime, then `x` and `y` can both be written
  as the product of a power of `p` and a divisor of `a`. -/
theorem mul_eq_mul_prime_pow {x y a p : R} {n : ℕ} (hp : Prime p) (hx : (x*y) = a*p ^ n) :
  ∃ (i j : ℕ)(b c : R), (i+j) = n ∧ (a = b*c) ∧ (x = b*p ^ i) ∧ y = c*p ^ j :=
  by 
    rcases
      mul_eq_mul_prime_prod (fun _ _ => hp)
        (show (x*y) = a*(range n).Prod fun _ => p by 
          simpa) with
      ⟨t, u, b, c, htus, htu, rfl, rfl, rfl⟩
    exact
      ⟨t.card, u.card, b, c,
        by 
          rw [←card_disjoint_union htu, htus, card_range],
        by 
          simp ⟩

end CommCancelMonoidWithZero

section CommRingₓ

variable {α : Type _} [CommRingₓ α]

theorem Prime.neg {p : α} (hp : Prime p) : Prime (-p) :=
  by 
    obtain ⟨h1, h2, h3⟩ := hp 
    exact
      ⟨neg_ne_zero.mpr h1,
        by 
          rwa [IsUnit.neg_iff],
        by 
          simpa [neg_dvd] using h3⟩

theorem Prime.abs [LinearOrderₓ α] {p : α} (hp : Prime p) : Prime (abs p) :=
  by 
    obtain h | h := abs_choice p <;> rw [h]
    ·
      exact hp
    ·
      exact hp.neg

end CommRingₓ

