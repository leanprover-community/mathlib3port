import Mathbin.Order.Ideal 
import Mathbin.Order.Pfilter

/-!
# Prime ideals

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections require more
structure, such as a bottom element, a top element, or a join-semilattice structure.

- `order.ideal.prime_pair`: A pair of an `ideal` and a `pfilter` which form a partition of `P`.
  This is useful as giving the data of a prime ideal is the same as giving the data of a prime
  filter.
- `order.ideal.is_prime`: a predicate for prime ideals. Dual to the notion of a prime filter.
- `order.pfilter.is_prime`: a predicate for prime filters. Dual to the notion of a prime ideal.

## References

- <https://en.wikipedia.org/wiki/Ideal_(order_theory)>

## Tags

ideal, prime

-/


open Order.Pfilter

namespace Order

variable{P : Type _}

namespace Ideal

/-- A pair of an `ideal` and a `pfilter` which form a partition of `P`.
-/
@[nolint has_inhabited_instance]
structure prime_pair(P : Type _)[Preorderₓ P] where 
  i : ideal P 
  f : pfilter P 
  is_compl_I_F : IsCompl (I : Set P) F

namespace PrimePair

variable[Preorderₓ P](IF : prime_pair P)

theorem compl_I_eq_F : «expr ᶜ» (IF.I : Set P) = IF.F :=
  IF.is_compl_I_F.compl_eq

theorem compl_F_eq_I : «expr ᶜ» (IF.F : Set P) = IF.I :=
  IF.is_compl_I_F.eq_compl.symm

theorem I_is_proper : is_proper IF.I :=
  by 
    cases IF.F.nonempty 
    apply is_proper_of_not_mem (_ : w ∉ IF.I)
    rwa [←IF.compl_I_eq_F] at h

theorem Disjoint : Disjoint (IF.I : Set P) IF.F :=
  IF.is_compl_I_F.disjoint

theorem I_union_F : (IF.I : Set P) ∪ IF.F = Set.Univ :=
  IF.is_compl_I_F.sup_eq_top

theorem F_union_I : (IF.F : Set P) ∪ IF.I = Set.Univ :=
  IF.is_compl_I_F.symm.sup_eq_top

end PrimePair

/-- An ideal `I` is prime if its complement is a filter.
-/
@[mkIff]
class is_prime[Preorderₓ P](I : ideal P) extends is_proper I : Prop where 
  compl_filter : is_pfilter («expr ᶜ» (I : Set P))

section Preorderₓ

variable[Preorderₓ P]

/-- Create an element of type `order.ideal.prime_pair` from an ideal satisfying the predicate
`order.ideal.is_prime`. -/
def is_prime.to_prime_pair {I : ideal P} (h : is_prime I) : prime_pair P :=
  { i, f := h.compl_filter.to_pfilter, is_compl_I_F := is_compl_compl }

theorem prime_pair.I_is_prime (IF : prime_pair P) : is_prime IF.I :=
  { IF.I_is_proper with
    compl_filter :=
      by 
        rw [IF.compl_I_eq_F]
        exact IF.F.is_pfilter }

end Preorderₓ

section SemilatticeInf

variable[SemilatticeInf P]{x y : P}{I : ideal P}

theorem is_prime.mem_or_mem (hI : is_prime I) {x y : P} : x⊓y ∈ I → x ∈ I ∨ y ∈ I :=
  by 
    contrapose! 
    let F := hI.compl_filter.to_pfilter 
    show x ∈ F ∧ y ∈ F → x⊓y ∈ F 
    exact fun h => inf_mem _ _ h.1 h.2

-- error in Order.PrimeIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_prime.of_mem_or_mem
[is_proper I]
(hI : ∀ {x y : P}, «expr ∈ »(«expr ⊓ »(x, y), I) → «expr ∨ »(«expr ∈ »(x, I), «expr ∈ »(y, I))) : is_prime I :=
begin
  rw [expr is_prime_iff] [],
  use [expr «expr‹ ›»(_)],
  apply [expr is_pfilter.of_def],
  { exact [expr set.nonempty_compl.2 (I.is_proper_iff.1 «expr‹ ›»(_))] },
  { intros [ident x, "_", ident y, "_"],
    refine [expr ⟨«expr ⊓ »(x, y), _, inf_le_left, inf_le_right⟩],
    have [] [] [":=", expr mt hI],
    tauto ["!"] },
  { exact [expr @mem_compl_of_ge _ _ _] }
end

theorem is_prime_iff_mem_or_mem [is_proper I] : is_prime I ↔ ∀ {x y : P}, x⊓y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨is_prime.mem_or_mem, is_prime.of_mem_or_mem⟩

end SemilatticeInf

section DistribLattice

variable[DistribLattice P]{I : ideal P}

-- error in Order.PrimeIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[priority 100] instance is_maximal.is_prime [is_maximal I] : is_prime I :=
begin
  rw [expr is_prime_iff_mem_or_mem] [],
  intros [ident x, ident y],
  contrapose ["!"] [],
  rintro ["⟨", ident hx, ",", ident hynI, "⟩", ident hxy],
  apply [expr hynI],
  let [ident J] [] [":=", expr «expr ⊔ »(I, principal x)],
  have [ident hJuniv] [":", expr «expr = »((J : set P), set.univ)] [":=", expr is_maximal.maximal_proper (lt_sup_principal_of_not_mem «expr‹ ›»(_))],
  have [ident hyJ] [":", expr «expr ∈ »(y, «expr↑ »(J))] [":=", expr set.eq_univ_iff_forall.mp hJuniv y],
  rw [expr coe_sup_eq] ["at", ident hyJ],
  rcases [expr hyJ, "with", "⟨", ident a, ",", ident ha, ",", ident b, ",", ident hb, ",", ident hy, "⟩"],
  rw [expr hy] [],
  apply [expr sup_mem _ _ ha],
  refine [expr I.mem_of_le (le_inf hb _) hxy],
  rw [expr hy] [],
  exact [expr le_sup_right]
end

end DistribLattice

section BooleanAlgebra

variable[BooleanAlgebra P]{x : P}{I : ideal P}

theorem is_prime.mem_or_compl_mem (hI : is_prime I) : x ∈ I ∨ «expr ᶜ» x ∈ I :=
  by 
    apply hI.mem_or_mem 
    rw [inf_compl_eq_bot]
    exact bot_mem

theorem is_prime.mem_compl_of_not_mem (hI : is_prime I) (hxnI : x ∉ I) : «expr ᶜ» x ∈ I :=
  hI.mem_or_compl_mem.resolve_left hxnI

-- error in Order.PrimeIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_prime_of_mem_or_compl_mem
[is_proper I]
(h : ∀ {x : P}, «expr ∨ »(«expr ∈ »(x, I), «expr ∈ »(«expr ᶜ»(x), I))) : is_prime I :=
begin
  simp [] [] ["only"] ["[", expr is_prime_iff_mem_or_mem, ",", expr or_iff_not_imp_left, "]"] [] [],
  intros [ident x, ident y, ident hxy, ident hxI],
  have [ident hxcI] [":", expr «expr ∈ »(«expr ᶜ»(x), I)] [":=", expr h.resolve_left hxI],
  have [ident ass] [":", expr «expr ∈ »(«expr ⊔ »(«expr ⊓ »(x, y), «expr ⊓ »(y, «expr ᶜ»(x))), I)] [":=", expr sup_mem _ _ hxy (mem_of_le I inf_le_right hxcI)],
  rwa ["[", expr inf_comm, ",", expr sup_inf_inf_compl, "]"] ["at", ident ass]
end

theorem is_prime_iff_mem_or_compl_mem [is_proper I] : is_prime I ↔ ∀ {x : P}, x ∈ I ∨ «expr ᶜ» x ∈ I :=
  ⟨fun h _ => h.mem_or_compl_mem, is_prime_of_mem_or_compl_mem⟩

instance (priority := 100)is_prime.is_maximal [is_prime I] : is_maximal I :=
  by 
    simp only [is_maximal_iff, Set.eq_univ_iff_forall, is_prime.to_is_proper, true_andₓ]
    intro J hIJ x 
    rcases Set.exists_of_ssubset hIJ with ⟨y, hyJ, hyI⟩
    suffices ass : x⊓y⊔x⊓«expr ᶜ» y ∈ J
    ·
      rwa [sup_inf_inf_compl] at ass 
    exact
      sup_mem _ _ (J.mem_of_le inf_le_right hyJ)
        (hIJ.le (I.mem_of_le inf_le_right (is_prime.mem_compl_of_not_mem ‹_› hyI)))

end BooleanAlgebra

end Ideal

namespace Pfilter

variable[Preorderₓ P]

/-- A filter `F` is prime if its complement is an ideal.
-/
@[mkIff]
class is_prime(F : pfilter P) : Prop where 
  compl_ideal : is_ideal («expr ᶜ» (F : Set P))

/-- Create an element of type `order.ideal.prime_pair` from a filter satisfying the predicate
`order.pfilter.is_prime`. -/
def is_prime.to_prime_pair {F : pfilter P} (h : is_prime F) : ideal.prime_pair P :=
  { i := h.compl_ideal.to_ideal, f, is_compl_I_F := is_compl_compl.symm }

theorem _root_.order.ideal.prime_pair.F_is_prime (IF : ideal.prime_pair P) : is_prime IF.F :=
  { compl_ideal :=
      by 
        rw [IF.compl_F_eq_I]
        exact IF.I.is_ideal }

end Pfilter

end Order

