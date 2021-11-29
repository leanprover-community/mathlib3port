import Mathbin.Topology.Separation

/-!
# The shrinking lemma

In this file we prove a few versions of the shrinking lemma. The lemma says that in a normal
topological space a point finite open covering can be “shrunk”: for a point finite open covering
`u : ι → set X` there exists a refinement `v : ι → set X` such that `closure (v i) ⊆ u i`.

For finite or countable coverings this lemma can be proved without the axiom of choice, see
[ncatlab](https://ncatlab.org/nlab/show/shrinking+lemma) for details. We only formalize the most
general result that works for any covering but needs the axiom of choice.

We prove two versions of the lemma:

* `exists_subset_Union_closure_subset` deals with a covering of a closed set in a normal space;
* `exists_Union_eq_closure_subset` deals with a covering of the whole space.

## Tags

normal space, shrinking lemma
-/


open Set Zorn Function

open_locale Classical

noncomputable theory

variable{ι X : Type _}[TopologicalSpace X][NormalSpace X]

namespace ShrinkingLemma

/-- Auxiliary definition for the proof of `shrinking_lemma`. A partial refinement of a covering
`⋃ i, u i` of a set `s` is a map `v : ι → set X` and a set `carrier : set ι` such that

* `s ⊆ ⋃ i, v i`;
* all `v i` are open;
* if `i ∈ carrier v`, then `closure (v i) ⊆ u i`;
* if `i ∉ carrier`, then `v i = u i`.

This type is equipped with the folowing partial order: `v ≤ v'` if `v.carrier ⊆ v'.carrier`
and `v i = v' i` for `i ∈ v.carrier`. We will use Zorn's lemma to prove that this type has
a maximal element, then show that the maximal element must have `carrier = univ`. -/
@[nolint has_inhabited_instance]
structure partial_refinement(u : ι → Set X)(s : Set X) where 
  toFun : ι → Set X 
  Carrier : Set ι 
  is_open' : ∀ i, IsOpen (to_fun i)
  subset_Union' : s ⊆ ⋃i, to_fun i 
  closure_subset' : ∀ i (_ : i ∈ carrier), Closure (to_fun i) ⊆ u i 
  apply_eq' : ∀ i (_ : i ∉ carrier), to_fun i = u i

namespace PartialRefinement

variable{u : ι → Set X}{s : Set X}

instance  : CoeFun (partial_refinement u s) fun _ => ι → Set X :=
  ⟨to_fun⟩

theorem subset_Union (v : partial_refinement u s) : s ⊆ ⋃i, v i :=
  v.subset_Union'

theorem closure_subset (v : partial_refinement u s) {i : ι} (hi : i ∈ v.carrier) : Closure (v i) ⊆ u i :=
  v.closure_subset' i hi

theorem apply_eq (v : partial_refinement u s) {i : ι} (hi : i ∉ v.carrier) : v i = u i :=
  v.apply_eq' i hi

protected theorem IsOpen (v : partial_refinement u s) (i : ι) : IsOpen (v i) :=
  v.is_open' i

protected theorem subset (v : partial_refinement u s) (i : ι) : v i ⊆ u i :=
  if h : i ∈ v.carrier then subset.trans subset_closure (v.closure_subset h) else (v.apply_eq h).le

attribute [ext] partial_refinement

instance  : PartialOrderₓ (partial_refinement u s) :=
  { le := fun v₁ v₂ => v₁.carrier ⊆ v₂.carrier ∧ ∀ i (_ : i ∈ v₁.carrier), v₁ i = v₂ i,
    le_refl := fun v => ⟨subset.refl _, fun _ _ => rfl⟩,
    le_trans := fun v₁ v₂ v₃ h₁₂ h₂₃ => ⟨subset.trans h₁₂.1 h₂₃.1, fun i hi => (h₁₂.2 i hi).trans (h₂₃.2 i$ h₁₂.1 hi)⟩,
    le_antisymm :=
      fun v₁ v₂ h₁₂ h₂₁ =>
        have hc : v₁.carrier = v₂.carrier := subset.antisymm h₁₂.1 h₂₁.1 
        ext _ _
          (funext$
            fun x => if hx : x ∈ v₁.carrier then h₁₂.2 _ hx else (v₁.apply_eq hx).trans (Eq.symm$ v₂.apply_eq$ hc ▸ hx))
          hc }

/-- If two partial refinements `v₁`, `v₂` belong to a chain (hence, they are comparable)
and `i` belongs to the carriers of both partial refinements, then `v₁ i = v₂ i`. -/
theorem apply_eq_of_chain {c : Set (partial_refinement u s)} (hc : chain (· ≤ ·) c) {v₁ v₂} (h₁ : v₁ ∈ c) (h₂ : v₂ ∈ c)
  {i} (hi₁ : i ∈ v₁.carrier) (hi₂ : i ∈ v₂.carrier) : v₁ i = v₂ i :=
  by 
    wlog hle : v₁ ≤ v₂ := hc.total_of_refl h₁ h₂ using v₁ v₂, v₂ v₁ 
    exact hle.2 _ hi₁

/-- The carrier of the least upper bound of a non-empty chain of partial refinements
is the union of their carriers. -/
def chain_Sup_carrier (c : Set (partial_refinement u s)) : Set ι :=
  ⋃(v : _)(_ : v ∈ c), carrier v

/-- Choice of an element of a nonempty chain of partial refinements. If `i` belongs to one of
`carrier v`, `v ∈ c`, then `find c ne i` is one of these partial refinements. -/
def find (c : Set (partial_refinement u s)) (ne : c.nonempty) (i : ι) : partial_refinement u s :=
  if hi : ∃ (v : _)(_ : v ∈ c), i ∈ carrier v then hi.some else ne.some

theorem find_mem {c : Set (partial_refinement u s)} (i : ι) (ne : c.nonempty) : find c Ne i ∈ c :=
  by 
    rw [find]
    splitIfs 
    exacts[h.some_spec.fst, ne.some_spec]

-- error in Topology.ShrinkingLemma: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_find_carrier_iff
{c : set (partial_refinement u s)}
{i : ι}
(ne : c.nonempty) : «expr ↔ »(«expr ∈ »(i, (find c ne i).carrier), «expr ∈ »(i, chain_Sup_carrier c)) :=
begin
  rw [expr find] [],
  split_ifs [] [],
  { have [] [":", expr «expr ∧ »(«expr ∈ »(i, h.some.carrier), «expr ∈ »(i, chain_Sup_carrier c))] [],
    from [expr ⟨h.some_spec.snd, mem_bUnion_iff.2 h⟩],
    simp [] [] ["only"] ["[", expr this, "]"] [] [] },
  { have [] [":", expr «expr ∧ »(«expr ∉ »(i, ne.some.carrier), «expr ∉ »(i, chain_Sup_carrier c))] [],
    from [expr ⟨λ hi, h ⟨_, ne.some_spec, hi⟩, mt mem_bUnion_iff.1 h⟩],
    simp [] [] ["only"] ["[", expr this, "]"] [] [] }
end

theorem find_apply_of_mem {c : Set (partial_refinement u s)} (hc : chain (· ≤ ·) c) (ne : c.nonempty) {i v} (hv : v ∈ c)
  (hi : i ∈ carrier v) : find c Ne i i = v i :=
  apply_eq_of_chain hc (find_mem _ _) hv ((mem_find_carrier_iff _).2$ mem_bUnion_iff.2 ⟨v, hv, hi⟩) hi

-- error in Topology.ShrinkingLemma: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Least upper bound of a nonempty chain of partial refinements. -/
def chain_Sup
(c : set (partial_refinement u s))
(hc : chain ((«expr ≤ »)) c)
(ne : c.nonempty)
(hfin : ∀ x «expr ∈ » s, finite {i | «expr ∈ »(x, u i)})
(hU : «expr ⊆ »(s, «expr⋃ , »((i), u i))) : partial_refinement u s :=
begin
  refine [expr ⟨λ
    i, find c ne i i, chain_Sup_carrier c, λ
    i, (find _ _ _).is_open i, λ
    x
    hxs, mem_Union.2 _, λ
    i
    hi, (find c ne i).closure_subset ((mem_find_carrier_iff _).2 hi), λ
    i hi, (find c ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi)⟩],
  rcases [expr em «expr∃ , »((i «expr ∉ » chain_Sup_carrier c), «expr ∈ »(x, u i)), "with", "⟨", ident i, ",", ident hi, ",", ident hxi, "⟩", "|", ident hx],
  { use [expr i],
    rwa [expr (find c ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi)] [] },
  { simp_rw ["[", expr not_exists, ",", expr not_imp_not, ",", expr chain_Sup_carrier, ",", expr mem_bUnion_iff, "]"] ["at", ident hx],
    haveI [] [":", expr nonempty (partial_refinement u s)] [":=", expr ⟨ne.some⟩],
    choose ["!"] [ident v] [ident hvc, ident hiv] ["using", expr hx],
    rcases [expr (hfin x hxs).exists_maximal_wrt v _ (mem_Union.1 (hU hxs)), "with", "⟨", ident i, ",", ident hxi, ":", expr «expr ∈ »(x, u i), ",", ident hmax, ":", expr ∀
     j, «expr ∈ »(x, u j) → «expr ≤ »(v i, v j) → «expr = »(v i, v j), "⟩"],
    rcases [expr mem_Union.1 ((v i).subset_Union hxs), "with", "⟨", ident j, ",", ident hj, "⟩"],
    use [expr j],
    have [ident hj'] [":", expr «expr ∈ »(x, u j)] [":=", expr (v i).subset _ hj],
    have [] [":", expr «expr ≤ »(v j, v i)] [],
    from [expr (hc.total_of_refl (hvc _ hxi) (hvc _ hj')).elim (λ h, (hmax j hj' h).ge) id],
    rwa [expr find_apply_of_mem hc ne (hvc _ hxi) «expr $ »(this.1, hiv _ hj')] [] }
end

/-- `chain_Sup hu c hc ne hfin hU` is an upper bound of the chain `c`. -/
theorem le_chain_Sup {c : Set (partial_refinement u s)} (hc : chain (· ≤ ·) c) (ne : c.nonempty)
  (hfin : ∀ x (_ : x ∈ s), finite { i | x ∈ u i }) (hU : s ⊆ ⋃i, u i) {v} (hv : v ∈ c) :
  v ≤ chain_Sup c hc Ne hfin hU :=
  ⟨fun i hi => mem_bUnion hv hi, fun i hi => (find_apply_of_mem hc _ hv hi).symm⟩

-- error in Topology.ShrinkingLemma: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `s` is a closed set, `v` is a partial refinement, and `i` is an index such that
`i ∉ v.carrier`, then there exists a partial refinement that is strictly greater than `v`. -/
theorem exists_gt
(v : partial_refinement u s)
(hs : is_closed s)
(i : ι)
(hi : «expr ∉ »(i, v.carrier)) : «expr∃ , »((v' : partial_refinement u s), «expr < »(v, v')) :=
begin
  have [ident I] [":", expr «expr ⊆ »(«expr ∩ »(s, «expr⋂ , »((j «expr ≠ » i), «expr ᶜ»(v j))), v i)] [],
  { simp [] [] ["only"] ["[", expr subset_def, ",", expr mem_inter_eq, ",", expr mem_Inter, ",", expr and_imp, "]"] [] [],
    intros [ident x, ident hxs, ident H],
    rcases [expr mem_Union.1 (v.subset_Union hxs), "with", "⟨", ident j, ",", ident hj, "⟩"],
    exact [expr (em «expr = »(j, i)).elim (λ h, «expr ▸ »(h, hj)) (λ h, (H j h hj).elim)] },
  have [ident C] [":", expr is_closed «expr ∩ »(s, «expr⋂ , »((j «expr ≠ » i), «expr ᶜ»(v j)))] [],
  from [expr is_closed.inter hs «expr $ »(is_closed_bInter, λ _ _, «expr $ »(is_closed_compl_iff.2, v.is_open _))],
  rcases [expr normal_exists_closure_subset C (v.is_open i) I, "with", "⟨", ident vi, ",", ident ovi, ",", ident hvi, ",", ident cvi, "⟩"],
  refine [expr ⟨⟨update v i vi, insert i v.carrier, _, _, _, _⟩, _, _⟩],
  { intro [ident j],
    by_cases [expr h, ":", expr «expr = »(j, i)]; simp [] [] [] ["[", expr h, ",", expr ovi, ",", expr v.is_open, "]"] [] [] },
  { refine [expr λ x hx, mem_Union.2 _],
    rcases [expr em «expr∃ , »((j «expr ≠ » i), «expr ∈ »(x, v j)), "with", "⟨", ident j, ",", ident hji, ",", ident hj, "⟩", "|", ident h],
    { use [expr j],
      rwa [expr update_noteq hji] [] },
    { push_neg ["at", ident h],
      use [expr i],
      rw [expr update_same] [],
      exact [expr hvi ⟨hx, mem_bInter h⟩] } },
  { rintro [ident j, "(", ident rfl, "|", ident hj, ")"],
    { rwa ["[", expr update_same, ",", "<-", expr v.apply_eq hi, "]"] [] },
    { rw [expr update_noteq (ne_of_mem_of_not_mem hj hi)] [],
      exact [expr v.closure_subset hj] } },
  { intros [ident j, ident hj],
    rw ["[", expr mem_insert_iff, ",", expr not_or_distrib, "]"] ["at", ident hj],
    rw ["[", expr update_noteq hj.1, ",", expr v.apply_eq hj.2, "]"] [] },
  { refine [expr ⟨subset_insert _ _, λ j hj, _⟩],
    exact [expr (update_noteq (ne_of_mem_of_not_mem hj hi) _ _).symm] },
  { exact [expr λ hle, hi «expr $ »(hle.1, mem_insert _ _)] }
end

end PartialRefinement

end ShrinkingLemma

open ShrinkingLemma

variable{u : ι → Set X}{s : Set X}

-- error in Topology.ShrinkingLemma: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new open cover so that the closure of each new open set is contained in the corresponding
original open set. -/
theorem exists_subset_Union_closure_subset
(hs : is_closed s)
(uo : ∀ i, is_open (u i))
(uf : ∀ x «expr ∈ » s, finite {i | «expr ∈ »(x, u i)})
(us : «expr ⊆ »(s, «expr⋃ , »((i), u i))) : «expr∃ , »((v : ι → set X), «expr ∧ »(«expr ⊆ »(s, Union v), «expr ∧ »(∀
   i, is_open (v i), ∀ i, «expr ⊆ »(closure (v i), u i)))) :=
begin
  classical,
  haveI [] [":", expr nonempty (partial_refinement u s)] [":=", expr ⟨⟨u, «expr∅»(), uo, us, λ
     _, false.elim, λ _ _, rfl⟩⟩],
  have [] [":", expr ∀
   c : set (partial_refinement u s), chain ((«expr ≤ »)) c → c.nonempty → «expr∃ , »((ub), ∀
    v «expr ∈ » c, «expr ≤ »(v, ub))] [],
  from [expr λ
   c hc ne, ⟨partial_refinement.chain_Sup c hc ne uf us, λ v hv, partial_refinement.le_chain_Sup _ _ _ _ hv⟩],
  rcases [expr zorn_nonempty_partial_order this, "with", "⟨", ident v, ",", ident hv, "⟩"],
  suffices [] [":", expr ∀ i, «expr ∈ »(i, v.carrier)],
  from [expr ⟨v, v.subset_Union, λ i, v.is_open _, λ i, v.closure_subset (this i)⟩],
  contrapose ["!"] [ident hv],
  rcases [expr hv, "with", "⟨", ident i, ",", ident hi, "⟩"],
  rcases [expr v.exists_gt hs i hi, "with", "⟨", ident v', ",", ident hlt, "⟩"],
  exact [expr ⟨v', hlt.le, hlt.ne'⟩]
end

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new closed cover so that each new closed set is contained in the corresponding original open
set. See also `exists_subset_Union_closure_subset` for a stronger statement. -/
theorem exists_subset_Union_closed_subset (hs : IsClosed s) (uo : ∀ i, IsOpen (u i))
  (uf : ∀ x (_ : x ∈ s), finite { i | x ∈ u i }) (us : s ⊆ ⋃i, u i) :
  ∃ v : ι → Set X, s ⊆ Union v ∧ (∀ i, IsClosed (v i)) ∧ ∀ i, v i ⊆ u i :=
  let ⟨v, hsv, hvo, hv⟩ := exists_subset_Union_closure_subset hs uo uf us
  ⟨fun i => Closure (v i), subset.trans hsv (Union_subset_Union$ fun i => subset_closure), fun i => is_closed_closure,
    hv⟩

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new open cover so that the closure of each new open set is contained in the corresponding
original open set. -/
theorem exists_Union_eq_closure_subset (uo : ∀ i, IsOpen (u i)) (uf : ∀ x, finite { i | x ∈ u i })
  (uU : (⋃i, u i) = univ) : ∃ v : ι → Set X, Union v = univ ∧ (∀ i, IsOpen (v i)) ∧ ∀ i, Closure (v i) ⊆ u i :=
  let ⟨v, vU, hv⟩ := exists_subset_Union_closure_subset is_closed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new closed cover so that each of the new closed sets is contained in the corresponding
original open set. See also `exists_Union_eq_closure_subset` for a stronger statement. -/
theorem exists_Union_eq_closed_subset (uo : ∀ i, IsOpen (u i)) (uf : ∀ x, finite { i | x ∈ u i })
  (uU : (⋃i, u i) = univ) : ∃ v : ι → Set X, Union v = univ ∧ (∀ i, IsClosed (v i)) ∧ ∀ i, v i ⊆ u i :=
  let ⟨v, vU, hv⟩ := exists_subset_Union_closed_subset is_closed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩

