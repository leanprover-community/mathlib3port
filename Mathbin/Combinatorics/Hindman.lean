import Mathbin.Topology.StoneCech 
import Mathbin.Topology.Algebra.Semigroup 
import Mathbin.Data.Stream.Basic

/-!
# Hindman's theorem on finite sums

We prove Hindman's theorem on finite sums, using idempotent ultrafilters.

Given an infinite sequence `a₀, a₁, a₂, …` of positive integers, the set `FS(a₀, …)` is the set
of positive integers that can be expressed as a finite sum of `aᵢ`'s, without repetition. Hindman's
theorem asserts that whenever the positive integers are finitely colored, there exists a sequence
`a₀, a₁, a₂, …` such that `FS(a₀, …)` is monochromatic. There is also a stronger version, saying
that whenever a set of the form `FS(a₀, …)` is finitely colored, there exists a sequence
`b₀, b₁, b₂, …` such that `FS(b₀, …)` is monochromatic and contained in `FS(a₀, …)`. We prove both
these versions for a general semigroup `M` instead of `ℕ+` since it is no harder, although this
special case implies the general case.

The idea of the proof is to extend the addition `(+) : M → M → M` to addition `(+) : βM → βM → βM`
on the space `βM` of ultrafilters on `M`. One can prove that if `U` is an _idempotent_ ultrafilter,
i.e. `U + U = U`, then any `U`-large subset of `M` contains some set `FS(a₀, …)` (see
`exists_FS_of_large`). And with the help of a general topological argument one can show that any set
of the form `FS(a₀, …)` is `U`-large according to some idempotent ultrafilter `U` (see
`exists_idempotent_ultrafilter_le_FS`). This is enough to prove the theorem since in any finite
partition of a `U`-large set, one of the parts is `U`-large.

## Main results

- `FS_partition_regular`: the strong form of Hindman's theorem
- `exists_FS_of_finite_cover`: the weak form of Hindman's theorem

## Tags

Ramsey theory, ultrafilter

-/


open Filter

/-- Multiplication of ultrafilters given by `∀ᶠ m in U*V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m*m')`. -/
@[toAdditive "Addition of ultrafilters given by\n`∀ᶠ m in U+V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m+m')`."]
def Ultrafilter.hasMul {M} [Mul M] : Mul (Ultrafilter M) :=
  { mul := fun U V => ((·*·) <$> U)<*>V }

attribute [local instance] Ultrafilter.hasMul Ultrafilter.hasAdd

@[toAdditive]
theorem Ultrafilter.eventually_mul {M} [Mul M] (U V : Ultrafilter M) (p : M → Prop) :
  (∀ᶠm in «expr↑ » (U*V), p m) ↔ ∀ᶠm in U, ∀ᶠm' in V, p (m*m') :=
  Iff.rfl

/-- Semigroup structure on `ultrafilter M` induced by a semigroup structure on `M`. -/
@[toAdditive "Additive semigroup structure on `ultrafilter M` induced by an additive semigroup\nstructure on `M`."]
def Ultrafilter.semigroup {M} [Semigroupₓ M] : Semigroupₓ (Ultrafilter M) :=
  { Ultrafilter.hasMul with
    mul_assoc :=
      fun U V W =>
        Ultrafilter.coe_inj.mp$
          Filter.ext'$
            fun p =>
              by 
                simp only [Ultrafilter.eventually_mul, mul_assocₓ] }

attribute [local instance] Ultrafilter.semigroup Ultrafilter.addSemigroup

@[toAdditive]
theorem Ultrafilter.continuous_mul_left {M} [Semigroupₓ M] (V : Ultrafilter M) : Continuous (·*V) :=
  TopologicalSpace.IsTopologicalBasis.continuous ultrafilter_basis_is_basis _$
    Set.forall_range_iff.mpr$ fun s => ultrafilter_is_open_basic { m:M | ∀ᶠm' in V, (m*m') ∈ s }

namespace Hindman

/-- `FS a` is the set of finite sums in `a`, i.e. `m ∈ FS a` if `m` is the sum of a nonempty
subsequence of `a`. We give a direct inductive definition instead of talking about subsequences. -/
inductive FS {M} [AddSemigroupₓ M] : Streamₓ M → Set M
  | head (a : Streamₓ M) : FS a a.head
  | tail (a : Streamₓ M) (m : M) (h : FS a.tail m) : FS a m
  | cons (a : Streamₓ M) (m : M) (h : FS a.tail m) : FS a (a.head+m)

/-- `FP a` is the set of finite products in `a`, i.e. `m ∈ FP a` if `m` is the product of a nonempty
subsequence of `a`. We give a direct inductive definition instead of talking about subsequences. -/
@[toAdditive FS]
inductive FP {M} [Semigroupₓ M] : Streamₓ M → Set M
  | head (a : Streamₓ M) : FP a a.head
  | tail (a : Streamₓ M) (m : M) (h : FP a.tail m) : FP a m
  | cons (a : Streamₓ M) (m : M) (h : FP a.tail m) : FP a (a.head*m)

/-- If `m` and `m'` are finite products in `M`, then so is `m * m'`, provided that `m'` is obtained
from a subsequence of `M` starting sufficiently late. -/
@[toAdditive]
theorem FP.mul {M} [Semigroupₓ M] {a : Streamₓ M} {m : M} (hm : m ∈ FP a) :
  ∃ n, ∀ m' _ : m' ∈ FP (a.drop n), (m*m') ∈ FP a :=
  by 
    induction' hm with a a m hm ih a m hm ih
    ·
      exact ⟨1, fun m hm => FP.cons a m hm⟩
    ·
      cases' ih with n hn 
      use n+1
      intro m' hm' 
      exact FP.tail _ _ (hn _ hm')
    ·
      cases' ih with n hn 
      use n+1
      intro m' hm' 
      rw [mul_assocₓ]
      exact FP.cons _ _ (hn _ hm')

@[toAdditive exists_idempotent_ultrafilter_le_FS]
theorem exists_idempotent_ultrafilter_le_FP {M} [Semigroupₓ M] (a : Streamₓ M) :
  ∃ U : Ultrafilter M, (U*U) = U ∧ ∀ᶠm in U, m ∈ FP a :=
  by 
    let S : Set (Ultrafilter M) := ⋂n, { U | ∀ᶠm in U, m ∈ FP (a.drop n) }
    obtain ⟨U, hU, U_idem⟩ := exists_idempotent_in_compact_subsemigroup _ S _ _ _
    ·
      refine' ⟨U, U_idem, _⟩
      convert set.mem_Inter.mp hU 0
    ·
      exact Ultrafilter.continuous_mul_left
    ·
      apply IsCompact.nonempty_Inter_of_sequence_nonempty_compact_closed
      ·
        intro n U hU 
        apply eventually.mono hU 
        rw [add_commₓ, ←Streamₓ.drop_drop, ←Streamₓ.tail_eq_drop]
        exact FP.tail _
      ·
        intro n 
        exact ⟨pure _, mem_pure.mpr$ FP.head _⟩
      ·
        exact (ultrafilter_is_closed_basic _).IsCompact
      ·
        intro n 
        apply ultrafilter_is_closed_basic
    ·
      exact IsClosed.is_compact (is_closed_Inter$ fun i => ultrafilter_is_closed_basic _)
    ·
      intro U V hU hV 
      rw [Set.mem_Inter] at *
      intro n 
      rw [Set.mem_set_of_eq, Ultrafilter.eventually_mul]
      apply eventually.mono (hU n)
      intro m hm 
      obtain ⟨n', hn⟩ := FP.mul hm 
      apply eventually.mono (hV (n'+n))
      intro m' hm' 
      apply hn 
      simpa only [Streamₓ.drop_drop] using hm'

-- error in Combinatorics.Hindman: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident exists_FS_of_large]]
theorem exists_FP_of_large
{M}
[semigroup M]
(U : ultrafilter M)
(U_idem : «expr = »(«expr * »(U, U), U))
(s₀ : set M)
(sU : «expr ∈ »(s₀, U)) : «expr∃ , »((a), «expr ⊆ »(FP a, s₀)) :=
begin
  have [ident exists_elem] [":", expr ∀
   {s : set M}
   (hs : «expr ∈ »(s, U)), «expr ∩ »(s, {m | «expr∀ᶠ in , »((m'), U, «expr ∈ »(«expr * »(m, m'), s))}).nonempty] [":=", expr λ
   s
   hs, ultrafilter.nonempty_of_mem «expr $ »(inter_mem hs, by { rw ["<-", expr U_idem] ["at", ident hs],
      exact [expr hs] })],
  let [ident elem] [":", expr {s // «expr ∈ »(s, U)} → M] [":=", expr λ p, (exists_elem p.property).some],
  let [ident succ] [":", expr {s // «expr ∈ »(s, U)} → {s // «expr ∈ »(s, U)}] [":=", expr λ
   p, ⟨«expr ∩ »(p.val, {m | «expr ∈ »(«expr * »(elem p, m), p.val)}), «expr $ »(inter_mem p.2, show _, from set.inter_subset_right _ _ (exists_elem p.2).some_mem)⟩],
  use [expr stream.corec elem succ (subtype.mk s₀ sU)],
  suffices [] [":", expr ∀
   (a : stream M)
   (m «expr ∈ » FP a), ∀ p, «expr = »(a, stream.corec elem succ p) → «expr ∈ »(m, p.val)],
  { intros [ident m, ident hm],
    exact [expr this _ m hm ⟨s₀, sU⟩ rfl] },
  clear [ident sU, ident s₀],
  intros [ident a, ident m, ident h],
  induction [expr h] [] ["with", ident b, ident b, ident n, ident h, ident ih, ident b, ident n, ident h, ident ih] [],
  { rintros [ident p, ident rfl],
    rw ["[", expr stream.corec_eq, ",", expr stream.head_cons, "]"] [],
    exact [expr set.inter_subset_left _ _ (set.nonempty.some_mem _)] },
  { rintros [ident p, ident rfl],
    refine [expr set.inter_subset_left _ _ (ih (succ p) _)],
    rw ["[", expr stream.corec_eq, ",", expr stream.tail_cons, "]"] [] },
  { rintros [ident p, ident rfl],
    have [] [] [":=", expr set.inter_subset_right _ _ (ih (succ p) _)],
    { simpa [] [] ["only"] [] [] ["using", expr this] },
    rw ["[", expr stream.corec_eq, ",", expr stream.tail_cons, "]"] [] }
end

/-- The strong form of **Hindman's theorem**: in any finite cover of an FP-set, one the parts
contains an FP-set. -/
@[toAdditive FS_partition_regular]
theorem FP_partition_regular {M} [Semigroupₓ M] (a : Streamₓ M) (s : Set (Set M)) (sfin : s.finite)
  (scov : FP a ⊆ ⋃₀s) : ∃ (c : _)(_ : c ∈ s)(b : Streamₓ M), FP b ⊆ c :=
  let ⟨U, idem, aU⟩ := exists_idempotent_ultrafilter_le_FP a 
  let ⟨c, cs, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset aU scov)
  ⟨c, cs, exists_FP_of_large U idem c hc⟩

/-- The weak form of **Hindman's theorem**: in any finite cover of a nonempty semigroup, one of the
parts contains an FP-set. -/
@[toAdditive exists_FS_of_finite_cover]
theorem exists_FP_of_finite_cover {M} [Semigroupₓ M] [Nonempty M] (s : Set (Set M)) (sfin : s.finite) (scov : ⊤ ⊆ ⋃₀s) :
  ∃ (c : _)(_ : c ∈ s)(a : Streamₓ M), FP a ⊆ c :=
  let ⟨U, hU⟩ := exists_idempotent_of_compact_t2_of_continuous_mul_left (@Ultrafilter.continuous_mul_left M _)
  let ⟨c, c_s, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset univ_mem scov)
  ⟨c, c_s, exists_FP_of_large U hU c hc⟩

@[toAdditive FS_iter_tail_sub_FS]
theorem FP_drop_subset_FP {M} [Semigroupₓ M] (a : Streamₓ M) (n : ℕ) : FP (a.drop n) ⊆ FP a :=
  by 
    induction' n with n ih
    ·
      rfl 
    rw [Nat.succ_eq_one_add, ←Streamₓ.drop_drop]
    exact trans (FP.tail _) ih

@[toAdditive]
theorem FP.singleton {M} [Semigroupₓ M] (a : Streamₓ M) (i : ℕ) : a.nth i ∈ FP a :=
  by 
    induction' i with i ih generalizing a
    ·
      apply FP.head
    ·
      apply FP.tail 
      apply ih

-- error in Combinatorics.Hindman: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem FP.mul_two
{M}
[semigroup M]
(a : stream M)
(i j : exprℕ())
(ij : «expr < »(i, j)) : «expr ∈ »(«expr * »(a.nth i, a.nth j), FP a) :=
begin
  refine [expr FP_drop_subset_FP _ i _],
  rw ["<-", expr stream.head_drop] [],
  apply [expr FP.cons],
  rcases [expr le_iff_exists_add.mp (nat.succ_le_of_lt ij), "with", "⟨", ident d, ",", ident hd, "⟩"],
  have [] [] [":=", expr FP.singleton (a.drop i).tail d],
  rw ["[", expr stream.tail_eq_drop, ",", expr stream.nth_drop, ",", expr stream.nth_drop, "]"] ["at", ident this],
  convert [] [expr this] [],
  rw ["[", expr hd, ",", expr add_comm, ",", expr nat.succ_add, ",", expr nat.add_succ, "]"] []
end

-- error in Combinatorics.Hindman: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem FP.finset_prod
{M}
[comm_monoid M]
(a : stream M)
(s : finset exprℕ())
(hs : s.nonempty) : «expr ∈ »(s.prod (λ i, a.nth i), FP a) :=
begin
  refine [expr FP_drop_subset_FP _ (s.min' hs) _],
  induction [expr s] ["using", ident finset.strong_induction] ["with", ident s, ident ih] [],
  rw ["[", "<-", expr finset.mul_prod_erase _ _ (s.min'_mem hs), ",", "<-", expr stream.head_drop, "]"] [],
  cases [expr (s.erase (s.min' hs)).eq_empty_or_nonempty] ["with", ident h, ident h],
  { rw ["[", expr h, ",", expr finset.prod_empty, ",", expr mul_one, "]"] [],
    exact [expr FP.head _] },
  { apply [expr FP.cons],
    rw ["[", expr stream.tail_eq_drop, ",", expr stream.drop_drop, ",", expr add_comm, "]"] [],
    refine [expr set.mem_of_subset_of_mem _ (ih _ «expr $ »(finset.erase_ssubset, s.min'_mem hs) h)],
    have [] [":", expr «expr ≤ »(«expr + »(s.min' hs, 1), (s.erase (s.min' hs)).min' h)] [":=", expr nat.succ_le_of_lt «expr $ »(finset.min'_lt_of_mem_erase_min' _ _, finset.min'_mem _ _)],
    cases [expr le_iff_exists_add.mp this] ["with", ident d, ident hd],
    rw ["[", expr hd, ",", expr add_comm, ",", "<-", expr stream.drop_drop, "]"] [],
    apply [expr FP_drop_subset_FP] }
end

end Hindman

