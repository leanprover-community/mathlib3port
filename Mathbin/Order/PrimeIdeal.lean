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

variable {P : Type _}

namespace Ideal

/-- A pair of an `ideal` and a `pfilter` which form a partition of `P`.
-/
@[nolint has_inhabited_instance]
structure prime_pair (P : Type _) [Preorderₓ P] where 
  i : ideal P 
  f : pfilter P 
  is_compl_I_F : IsCompl (I : Set P) F

namespace PrimePair

variable [Preorderₓ P] (IF : prime_pair P)

theorem compl_I_eq_F : (IF.I : Set P)ᶜ = IF.F :=
  IF.is_compl_I_F.compl_eq

theorem compl_F_eq_I : (IF.F : Set P)ᶜ = IF.I :=
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
class is_prime [Preorderₓ P] (I : ideal P) extends is_proper I : Prop where 
  compl_filter : is_pfilter ((I : Set P)ᶜ)

section Preorderₓ

variable [Preorderₓ P]

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

variable [SemilatticeInf P] {x y : P} {I : ideal P}

theorem is_prime.mem_or_mem (hI : is_prime I) {x y : P} : x⊓y ∈ I → x ∈ I ∨ y ∈ I :=
  by 
    contrapose! 
    let F := hI.compl_filter.to_pfilter 
    show x ∈ F ∧ y ∈ F → x⊓y ∈ F 
    exact fun h => inf_mem _ _ h.1 h.2

theorem is_prime.of_mem_or_mem [is_proper I] (hI : ∀ {x y : P}, x⊓y ∈ I → x ∈ I ∨ y ∈ I) : is_prime I :=
  by 
    rw [is_prime_iff]
    use ‹_›
    apply is_pfilter.of_def
    ·
      exact Set.nonempty_compl.2 (I.is_proper_iff.1 ‹_›)
    ·
      intro x _ y _ 
      refine' ⟨x⊓y, _, inf_le_left, inf_le_right⟩
      have  := mt hI 
      tauto!
    ·
      exact @mem_compl_of_ge _ _ _

theorem is_prime_iff_mem_or_mem [is_proper I] : is_prime I ↔ ∀ {x y : P}, x⊓y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨is_prime.mem_or_mem, is_prime.of_mem_or_mem⟩

end SemilatticeInf

section DistribLattice

variable [DistribLattice P] {I : ideal P}

instance (priority := 100) is_maximal.is_prime [is_maximal I] : is_prime I :=
  by 
    rw [is_prime_iff_mem_or_mem]
    intro x y 
    contrapose! 
    rintro ⟨hx, hynI⟩ hxy 
    apply hynI 
    let J := I⊔principal x 
    have hJuniv : (J : Set P) = Set.Univ := is_maximal.maximal_proper (lt_sup_principal_of_not_mem ‹_›)
    have hyJ : y ∈ ↑J := set.eq_univ_iff_forall.mp hJuniv y 
    rw [coe_sup_eq] at hyJ 
    rcases hyJ with ⟨a, ha, b, hb, hy⟩
    rw [hy]
    apply sup_mem _ _ ha 
    refine' I.mem_of_le (le_inf hb _) hxy 
    rw [hy]
    exact le_sup_right

end DistribLattice

section BooleanAlgebra

variable [BooleanAlgebra P] {x : P} {I : ideal P}

theorem is_prime.mem_or_compl_mem (hI : is_prime I) : x ∈ I ∨ xᶜ ∈ I :=
  by 
    apply hI.mem_or_mem 
    rw [inf_compl_eq_bot]
    exact bot_mem

theorem is_prime.mem_compl_of_not_mem (hI : is_prime I) (hxnI : x ∉ I) : xᶜ ∈ I :=
  hI.mem_or_compl_mem.resolve_left hxnI

theorem is_prime_of_mem_or_compl_mem [is_proper I] (h : ∀ {x : P}, x ∈ I ∨ xᶜ ∈ I) : is_prime I :=
  by 
    simp only [is_prime_iff_mem_or_mem, or_iff_not_imp_left]
    intro x y hxy hxI 
    have hxcI : xᶜ ∈ I := h.resolve_left hxI 
    have ass : x⊓y⊔y⊓xᶜ ∈ I := sup_mem _ _ hxy (mem_of_le I inf_le_right hxcI)
    rwa [inf_comm, sup_inf_inf_compl] at ass

theorem is_prime_iff_mem_or_compl_mem [is_proper I] : is_prime I ↔ ∀ {x : P}, x ∈ I ∨ xᶜ ∈ I :=
  ⟨fun h _ => h.mem_or_compl_mem, is_prime_of_mem_or_compl_mem⟩

instance (priority := 100) is_prime.is_maximal [is_prime I] : is_maximal I :=
  by 
    simp only [is_maximal_iff, Set.eq_univ_iff_forall, is_prime.to_is_proper, true_andₓ]
    intro J hIJ x 
    rcases Set.exists_of_ssubset hIJ with ⟨y, hyJ, hyI⟩
    suffices ass : x⊓y⊔x⊓yᶜ ∈ J
    ·
      rwa [sup_inf_inf_compl] at ass 
    exact
      sup_mem _ _ (J.mem_of_le inf_le_right hyJ)
        (hIJ.le (I.mem_of_le inf_le_right (is_prime.mem_compl_of_not_mem ‹_› hyI)))

end BooleanAlgebra

end Ideal

namespace Pfilter

variable [Preorderₓ P]

/-- A filter `F` is prime if its complement is an ideal.
-/
@[mkIff]
class is_prime (F : pfilter P) : Prop where 
  compl_ideal : is_ideal ((F : Set P)ᶜ)

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

