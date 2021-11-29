import Mathbin.Order.Lattice 
import Mathbin.Data.List.Sort 
import Mathbin.Data.Equiv.Fin 
import Mathbin.Data.Equiv.Functor

/-!
# Jordan-Hölder Theorem

This file proves the Jordan Hölder theorem for a `jordan_holder_lattice`, a class also defined in
this file. Examples of `jordan_holder_lattice` include `subgroup G` if `G` is a group, and
`submodule R M` if `M` is an `R`-module. Using this approach the theorem need not be proved
seperately for both groups and modules, the proof in this file can be applied to both.

## Main definitions
The main definitions in this file are `jordan_holder_lattice` and `composition_series`,
and the relation `equivalent` on `composition_series`

A `jordan_holder_lattice` is the class for which the Jordan Hölder theorem is proved. A
Jordan Hölder lattice is a lattice equipped with a notion of maximality, `is_maximal`, and a notion
of isomorphism of pairs `iso`. In the example of subgroups of a group, `is_maximal H K` means that
`H` is a maximal normal subgroup of `K`, and `iso (H₁, K₁) (H₂, K₂)` means that the quotient
`H₁ / K₁` is isomorphic to the quotient `H₂ / K₂`. `iso` must be symmetric and transitive and must
satisfy the second isomorphism theorem `iso (H, H ⊔ K) (H ⊓ K, K)`.

A `composition_series X` is a finite nonempty series of elements of the lattice `X` such that
each element is maximal inside the next. The length of a `composition_series X` is
one less than the number of elements in the series. Note that there is no stipulation
that a series start from the bottom of the lattice and finish at the top.
For a composition series `s`, `s.top` is the largest element of the series,
and `s.bot` is the least element.

Two `composition_series X`, `s₁` and `s₂` are equivalent if there is a bijection
`e : fin s₁.length ≃ fin s₂.length` such that for any `i`,
`iso (s₁ i, s₁ i.succ) (s₂ (e i), s₂ (e i.succ))`

## Main theorems

The main theorem is `composition_series.jordan_holder`, which says that if two composition
series have the same least element and the same largest element,
then they are `equivalent`.

## TODO

Provide instances of `jordan_holder_lattice` for both submodules and subgroups, and potentially
for modular lattices.

It is not entirely clear how this should be done. Possibly there should be no global instances
of `jordan_holder_lattice`, and the instances should only be defined locally in order to prove
the Jordan-Hölder theorem for modules/groups and the API should be transferred because many of the
theorems in this file will have stronger versions for modules. There will also need to be an API for
mapping composition series across homomorphisms. It is also probably possible to
provide an instance of `jordan_holder_lattice` for any `modular_lattice`, and in this case the
Jordan-Hölder theorem will say that there is a well defined notion of length of a modular lattice.
However an instance of `jordan_holder_lattice` for a modular lattice will not be able to contain
the correct notion of isomorphism for modules, so a separate instance for modules will still be
required and this will clash with the instance for modular lattices, and so at least one of these
instances should not be a global instance.
-/


universe u

open Set

/--
A `jordan_holder_lattice` is the class for which the Jordan Hölder theorem is proved. A
Jordan Hölder lattice is a lattice equipped with a notion of maximality, `is_maximal`, and a notion
of isomorphism of pairs `iso`. In the example of subgroups of a group, `is_maximal H K` means that
`H` is a maximal normal subgroup of `K`, and `iso (H₁, K₁) (H₂, K₂)` means that the quotient
`H₁ / K₁` is isomorphic to the quotient `H₂ / K₂`. `iso` must be symmetric and transitive and must
satisfy the second isomorphism theorem `iso (H, H ⊔ K) (H ⊓ K, K)`.
Examples include `subgroup G` if `G` is a group, and `submodule R M` if `M` is an `R`-module.
-/
class JordanHolderLattice(X : Type u)[Lattice X] where 
  IsMaximal : X → X → Prop 
  lt_of_is_maximal : ∀ {x y}, is_maximal x y → x < y 
  sup_eq_of_is_maximal : ∀ {x y z}, is_maximal x z → is_maximal y z → x ≠ y → x⊔y = z 
  is_maximal_inf_left_of_is_maximal_sup : ∀ {x y}, is_maximal x (x⊔y) → is_maximal y (x⊔y) → is_maximal (x⊓y) x 
  Iso : X × X → X × X → Prop 
  iso_symm : ∀ {x y}, iso x y → iso y x 
  iso_trans : ∀ {x y z}, iso x y → iso y z → iso x z 
  second_iso : ∀ {x y}, is_maximal x (x⊔y) → iso (x, x⊔y) (x⊓y, y)

namespace JordanHolderLattice

variable{X : Type u}[Lattice X][JordanHolderLattice X]

theorem is_maximal_inf_right_of_is_maximal_sup {x y : X} (hxz : is_maximal x (x⊔y)) (hyz : is_maximal y (x⊔y)) :
  is_maximal (x⊓y) y :=
  by 
    rw [inf_comm]
    rw [sup_comm] at hxz hyz 
    exact is_maximal_inf_left_of_is_maximal_sup hyz hxz

-- error in Order.JordanHolder: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_maximal_of_eq_inf
(x b : X)
{a y : X}
(ha : «expr = »(«expr ⊓ »(x, y), a))
(hxy : «expr ≠ »(x, y))
(hxb : is_maximal x b)
(hyb : is_maximal y b) : is_maximal a y :=
begin
  have [ident hb] [":", expr «expr = »(«expr ⊔ »(x, y), b)] [],
  from [expr sup_eq_of_is_maximal hxb hyb hxy],
  substs [ident a, ident b],
  exact [expr is_maximal_inf_right_of_is_maximal_sup hxb hyb]
end

theorem second_iso_of_eq {x y a b : X} (hm : is_maximal x a) (ha : x⊔y = a) (hb : x⊓y = b) : iso (x, a) (b, y) :=
  by 
    substs a b <;> exact second_iso hm

theorem is_maximal.iso_refl {x y : X} (h : is_maximal x y) : iso (x, y) (x, y) :=
  second_iso_of_eq h (sup_eq_right.2 (le_of_ltₓ (lt_of_is_maximal h))) (inf_eq_left.2 (le_of_ltₓ (lt_of_is_maximal h)))

end JordanHolderLattice

open JordanHolderLattice

attribute [symm] iso_symm

attribute [trans] iso_trans

/--
A `composition_series X` is a finite nonempty series of elements of a
`jordan_holder_lattice` such that each element is maximal inside the next. The length of a
`composition_series X` is one less than the number of elements in the series.
Note that there is no stipulation that a series start from the bottom of the lattice and finish at
the top. For a composition series `s`, `s.top` is the largest element of the series,
and `s.bot` is the least element.
-/
structure CompositionSeries(X : Type u)[Lattice X][JordanHolderLattice X] : Type u where 
  length : ℕ 
  series : Finₓ (length+1) → X 
  step' : ∀ (i : Finₓ length), is_maximal (series i.cast_succ) (series i.succ)

namespace CompositionSeries

variable{X : Type u}[Lattice X][JordanHolderLattice X]

instance  : CoeFun (CompositionSeries X) fun x => Finₓ (x.length+1) → X :=
  { coe := CompositionSeries.series }

instance  [Inhabited X] : Inhabited (CompositionSeries X) :=
  ⟨{ length := 0, series := fun _ => default X, step' := fun x => x.elim0 }⟩

variable{X}

theorem step (s : CompositionSeries X) : ∀ (i : Finₓ s.length), is_maximal (s i.cast_succ) (s i.succ) :=
  s.step'

@[simp]
theorem coe_fn_mk (length : ℕ) series step :
  (@CompositionSeries.mk X _ _ length series step : Finₓ length.succ → X) = series :=
  rfl

theorem lt_succ (s : CompositionSeries X) (i : Finₓ s.length) : s i.cast_succ < s i.succ :=
  lt_of_is_maximal (s.step _)

protected theorem StrictMono (s : CompositionSeries X) : StrictMono s :=
  Finₓ.strict_mono_iff_lt_succ.2 fun i h => s.lt_succ ⟨i, Nat.lt_of_succ_lt_succₓ h⟩

protected theorem injective (s : CompositionSeries X) : Function.Injective s :=
  s.strict_mono.injective

@[simp]
protected theorem inj (s : CompositionSeries X) {i j : Finₓ s.length.succ} : s i = s j ↔ i = j :=
  s.injective.eq_iff

instance  : HasMem X (CompositionSeries X) :=
  ⟨fun x s => x ∈ Set.Range s⟩

theorem mem_def {x : X} {s : CompositionSeries X} : x ∈ s ↔ x ∈ Set.Range s :=
  Iff.rfl

theorem Total {s : CompositionSeries X} {x y : X} (hx : x ∈ s) (hy : y ∈ s) : x ≤ y ∨ y ≤ x :=
  by 
    rcases Set.mem_range.1 hx with ⟨i, rfl⟩
    rcases Set.mem_range.1 hy with ⟨j, rfl⟩
    rw [s.strict_mono.le_iff_le, s.strict_mono.le_iff_le]
    exact le_totalₓ i j

/-- The ordered `list X` of elements of a `composition_series X`. -/
def to_list (s : CompositionSeries X) : List X :=
  List.ofFn s

/-- Two `composition_series` are equal if they are the same length and
have the same `i`th element for every `i` -/
theorem ext_fun {s₁ s₂ : CompositionSeries X} (hl : s₁.length = s₂.length)
  (h : ∀ i, s₁ i = s₂ (Finₓ.cast (congr_argₓ Nat.succ hl) i)) : s₁ = s₂ :=
  by 
    cases s₁ 
    cases s₂ 
    dsimp  at *
    subst hl 
    simpa [Function.funext_iffₓ] using h

@[simp]
theorem length_to_list (s : CompositionSeries X) : s.to_list.length = s.length+1 :=
  by 
    rw [to_list, List.length_of_fn]

theorem to_list_ne_nil (s : CompositionSeries X) : s.to_list ≠ [] :=
  by 
    rw [←List.length_pos_iff_ne_nilₓ, length_to_list] <;> exact Nat.succ_posₓ _

-- error in Order.JordanHolder: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem to_list_injective : function.injective (@composition_series.to_list X _ _) :=
λ
(s₁ s₂)
(h : «expr = »(list.of_fn s₁, list.of_fn s₂)), have h₁ : «expr = »(s₁.length, s₂.length), from nat.succ_injective «expr $ »((list.length_of_fn s₁).symm.trans, «expr $ »((congr_arg list.length h).trans, list.length_of_fn s₂)),
have h₂ : ∀ i : fin s₁.length.succ, «expr = »(s₁ i, s₂ (fin.cast (congr_arg nat.succ h₁) i)), begin
  assume [binders (i)],
  rw ["[", "<-", expr list.nth_le_of_fn s₁ i, ",", "<-", expr list.nth_le_of_fn s₂, "]"] [],
  simp [] [] [] ["[", expr h, "]"] [] []
end,
begin
  cases [expr s₁] [],
  cases [expr s₂] [],
  dsimp [] [] [] ["at", "*"],
  subst [expr h₁],
  simp [] [] ["only"] ["[", expr heq_iff_eq, ",", expr eq_self_iff_true, ",", expr true_and, "]"] [] [],
  simp [] [] ["only"] ["[", expr fin.cast_refl, "]"] [] ["at", ident h₂],
  exact [expr funext h₂]
end

theorem chain'_to_list (s : CompositionSeries X) : List.Chain' is_maximal s.to_list :=
  List.chain'_iff_nth_le.2
    (by 
      intro i hi 
      simp only [to_list, List.nth_le_of_fn']
      rw [length_to_list] at hi 
      exact s.step ⟨i, hi⟩)

theorem to_list_sorted (s : CompositionSeries X) : s.to_list.sorted (· < ·) :=
  List.pairwise_iff_nth_le.2
    fun i j hi hij =>
      by 
        dsimp [to_list]
        rw [List.nth_le_of_fn', List.nth_le_of_fn']
        exact s.strict_mono hij

theorem to_list_nodup (s : CompositionSeries X) : s.to_list.nodup :=
  List.nodup_iff_nth_le_inj.2
    fun i j hi hj =>
      by 
        delta' to_list 
        rw [List.nth_le_of_fn', List.nth_le_of_fn', s.injective.eq_iff, Finₓ.ext_iff, Finₓ.coe_mk, Finₓ.coe_mk]
        exact id

@[simp]
theorem mem_to_list {s : CompositionSeries X} {x : X} : x ∈ s.to_list ↔ x ∈ s :=
  by 
    rw [to_list, List.mem_of_fn, mem_def]

/-- Make a `composition_series X` from the ordered list of its elements. -/
def of_list (l : List X) (hl : l ≠ []) (hc : List.Chain' is_maximal l) : CompositionSeries X :=
  { length := l.length - 1,
    series :=
      fun i =>
        l.nth_le i
          (by 
            convRHS => rw [←tsub_add_cancel_of_le (Nat.succ_le_of_ltₓ (List.length_pos_of_ne_nilₓ hl))]
            exact i.2),
    step' := fun ⟨i, hi⟩ => List.chain'_iff_nth_le.1 hc i hi }

theorem length_of_list (l : List X) (hl : l ≠ []) (hc : List.Chain' is_maximal l) :
  (of_list l hl hc).length = l.length - 1 :=
  rfl

theorem of_list_to_list (s : CompositionSeries X) : of_list s.to_list s.to_list_ne_nil s.chain'_to_list = s :=
  by 
    refine' ext_fun _ _
    ·
      rw [length_of_list, length_to_list, Nat.succ_sub_one]
    ·
      rintro ⟨i, hi⟩
      dsimp [of_list, to_list]
      rw [List.nth_le_of_fn']

@[simp]
theorem of_list_to_list' (s : CompositionSeries X) : of_list s.to_list s.to_list_ne_nil s.chain'_to_list = s :=
  of_list_to_list s

@[simp]
theorem to_list_of_list (l : List X) (hl : l ≠ []) (hc : List.Chain' is_maximal l) : to_list (of_list l hl hc) = l :=
  by 
    refine' List.ext_le _ _
    ·
      rw [length_to_list, length_of_list, tsub_add_cancel_of_le (Nat.succ_le_of_ltₓ$ List.length_pos_of_ne_nilₓ hl)]
    ·
      intro i hi hi' 
      dsimp [of_list, to_list]
      rw [List.nth_le_of_fn']
      rfl

/-- Two `composition_series` are equal if they have the same elements. See also `ext_fun`. -/
@[ext]
theorem ext {s₁ s₂ : CompositionSeries X} (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ :=
  to_list_injective$
    List.eq_of_perm_of_sorted
      (by 
        classical <;>
          exact
            List.perm_of_nodup_nodup_to_finset_eq s₁.to_list_nodup s₂.to_list_nodup
              (Finset.ext$
                by 
                  simp ))
      s₁.to_list_sorted s₂.to_list_sorted

/-- The largest element of a `composition_series` -/
def top (s : CompositionSeries X) : X :=
  s (Finₓ.last _)

theorem top_mem (s : CompositionSeries X) : s.top ∈ s :=
  mem_def.2 (Set.mem_range.2 ⟨Finₓ.last _, rfl⟩)

@[simp]
theorem le_top {s : CompositionSeries X} (i : Finₓ (s.length+1)) : s i ≤ s.top :=
  s.strict_mono.monotone (Finₓ.le_last _)

theorem le_top_of_mem {s : CompositionSeries X} {x : X} (hx : x ∈ s) : x ≤ s.top :=
  let ⟨i, hi⟩ := Set.mem_range.2 hx 
  hi ▸ le_top _

/-- The smallest element of a `composition_series` -/
def bot (s : CompositionSeries X) : X :=
  s 0

theorem bot_mem (s : CompositionSeries X) : s.bot ∈ s :=
  mem_def.2 (Set.mem_range.2 ⟨0, rfl⟩)

@[simp]
theorem bot_le {s : CompositionSeries X} (i : Finₓ (s.length+1)) : s.bot ≤ s i :=
  s.strict_mono.monotone (Finₓ.zero_le _)

theorem bot_le_of_mem {s : CompositionSeries X} {x : X} (hx : x ∈ s) : s.bot ≤ x :=
  let ⟨i, hi⟩ := Set.mem_range.2 hx 
  hi ▸ bot_le _

theorem length_pos_of_mem_ne {s : CompositionSeries X} {x y : X} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
  0 < s.length :=
  let ⟨i, hi⟩ := hx 
  let ⟨j, hj⟩ := hy 
  have hij : i ≠ j := mt s.inj.2$ fun h => hxy (hi ▸ hj ▸ h)
  hij.lt_or_lt.elim (fun hij => lt_of_le_of_ltₓ (zero_le i) (lt_of_lt_of_leₓ hij (Nat.le_of_lt_succₓ j.2)))
    fun hji => lt_of_le_of_ltₓ (zero_le j) (lt_of_lt_of_leₓ hji (Nat.le_of_lt_succₓ i.2))

theorem forall_mem_eq_of_length_eq_zero {s : CompositionSeries X} (hs : s.length = 0) {x y} (hx : x ∈ s) (hy : y ∈ s) :
  x = y :=
  by_contradiction fun hxy => pos_iff_ne_zero.1 (length_pos_of_mem_ne hx hy hxy) hs

-- error in Order.JordanHolder: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Remove the largest element from a `composition_series`. If the series `s`
has length zero, then `s.erase_top = s` -/
@[simps #[]]
def erase_top (s : composition_series X) : composition_series X :=
{ length := «expr - »(s.length, 1),
  series := λ i, s ⟨i, lt_of_lt_of_le i.2 (nat.succ_le_succ tsub_le_self)⟩,
  step' := λ i, begin
    have [] [] [":=", expr s.step ⟨i, lt_of_lt_of_le i.2 tsub_le_self⟩],
    cases [expr i] [],
    exact [expr this]
  end }

theorem top_erase_top (s : CompositionSeries X) :
  s.erase_top.top = s ⟨s.length - 1, lt_of_le_of_ltₓ tsub_le_self (Nat.lt_succ_selfₓ _)⟩ :=
  show s _ = s _ from
    congr_argₓ s
      (by 
        ext 
        simp only [erase_top_length, Finₓ.coe_last, Finₓ.coe_cast_succ, Finₓ.coe_of_nat_eq_mod, Finₓ.coe_mk, coe_coe])

theorem erase_top_top_le (s : CompositionSeries X) : s.erase_top.top ≤ s.top :=
  by 
    simp [erase_top, top, s.strict_mono.le_iff_le, Finₓ.le_iff_coe_le_coe, tsub_le_self]

@[simp]
theorem bot_erase_top (s : CompositionSeries X) : s.erase_top.bot = s.bot :=
  rfl

-- error in Order.JordanHolder: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_erase_top_of_ne_of_mem
{s : composition_series X}
{x : X}
(hx : «expr ≠ »(x, s.top))
(hxs : «expr ∈ »(x, s)) : «expr ∈ »(x, s.erase_top) :=
begin
  { rcases [expr hxs, "with", "⟨", ident i, ",", ident rfl, "⟩"],
    have [ident hi] [":", expr «expr < »((i : exprℕ()), «expr - »(s.length, 1).succ)] [],
    { conv_rhs [] [] { rw ["[", "<-", expr nat.succ_sub (length_pos_of_mem_ne ⟨i, rfl⟩ s.top_mem hx), ",", expr nat.succ_sub_one, "]"] },
      exact [expr lt_of_le_of_ne (nat.le_of_lt_succ i.2) (by simpa [] [] [] ["[", expr top, ",", expr s.inj, ",", expr fin.ext_iff, "]"] [] ["using", expr hx])] },
    refine [expr ⟨i.cast_succ, _⟩],
    simp [] [] [] ["[", expr fin.ext_iff, ",", expr nat.mod_eq_of_lt hi, "]"] [] [] }
end

-- error in Order.JordanHolder: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_erase_top
{s : composition_series X}
{x : X}
(h : «expr < »(0, s.length)) : «expr ↔ »(«expr ∈ »(x, s.erase_top), «expr ∧ »(«expr ≠ »(x, s.top), «expr ∈ »(x, s))) :=
begin
  simp [] [] ["only"] ["[", expr mem_def, "]"] [] [],
  dsimp ["only"] ["[", expr erase_top, ",", expr coe_fn_mk, "]"] [] [],
  split,
  { rintros ["⟨", ident i, ",", ident rfl, "⟩"],
    have [ident hi] [":", expr «expr < »((i : exprℕ()), s.length)] [],
    { conv_rhs [] [] { rw ["[", "<-", expr nat.succ_sub_one s.length, ",", expr nat.succ_sub h, "]"] },
      exact [expr i.2] },
    simp [] [] [] ["[", expr top, ",", expr fin.ext_iff, ",", expr ne_of_lt hi, "]"] [] [] },
  { intro [ident h],
    exact [expr mem_erase_top_of_ne_of_mem h.1 h.2] }
end

theorem lt_top_of_mem_erase_top {s : CompositionSeries X} {x : X} (h : 0 < s.length) (hx : x ∈ s.erase_top) :
  x < s.top :=
  lt_of_le_of_neₓ (le_top_of_mem ((mem_erase_top h).1 hx).2) ((mem_erase_top h).1 hx).1

theorem is_maximal_erase_top_top {s : CompositionSeries X} (h : 0 < s.length) : is_maximal s.erase_top.top s.top :=
  have  : ((s.length - 1)+1) = s.length :=
    by 
      convRHS => rw [←Nat.succ_sub_one s.length] <;> rw [Nat.succ_subₓ h]
  by 
    rw [top_erase_top, top]
    convert s.step ⟨s.length - 1, Nat.sub_ltₓ h zero_lt_one⟩ <;> ext <;> simp [this]

theorem append_cast_add_aux {s₁ s₂ : CompositionSeries X} (i : Finₓ s₁.length) :
  Finₓ.append (Nat.add_succ _ _).symm (s₁ ∘ Finₓ.castSucc) s₂ (Finₓ.castAdd s₂.length i).cast_succ = s₁ i.cast_succ :=
  by 
    cases i 
    simp [Finₓ.append]

-- error in Order.JordanHolder: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem append_succ_cast_add_aux
{s₁ s₂ : composition_series X}
(i : fin s₁.length)
(h : «expr = »(s₁ (fin.last _), s₂ 0)) : «expr = »(fin.append (nat.add_succ _ _).symm «expr ∘ »(s₁, fin.cast_succ) s₂ (fin.cast_add s₂.length i).succ, s₁ i.succ) :=
begin
  cases [expr i] ["with", ident i, ident hi],
  simp [] [] ["only"] ["[", expr fin.append, ",", expr hi, ",", expr fin.succ_mk, ",", expr function.comp_app, ",", expr fin.cast_succ_mk, ",", expr fin.coe_mk, ",", expr fin.cast_add_mk, "]"] [] [],
  split_ifs [] [],
  { refl },
  { have [] [":", expr «expr = »(«expr + »(i, 1), s₁.length)] [],
    from [expr le_antisymm hi (le_of_not_gt h_1)],
    calc
      «expr = »(s₂ ⟨«expr - »(«expr + »(i, 1), s₁.length), by simp [] [] [] ["[", expr this, "]"] [] []⟩, s₂ 0) : congr_arg s₂ (by simp [] [] [] ["[", expr fin.ext_iff, ",", expr this, "]"] [] [])
      «expr = »(..., s₁ (fin.last _)) : h.symm
      «expr = »(..., _) : congr_arg s₁ (by simp [] [] [] ["[", expr fin.ext_iff, ",", expr this, "]"] [] []) }
end

theorem append_nat_add_aux {s₁ s₂ : CompositionSeries X} (i : Finₓ s₂.length) :
  Finₓ.append (Nat.add_succ _ _).symm (s₁ ∘ Finₓ.castSucc) s₂ (Finₓ.natAdd s₁.length i).cast_succ = s₂ i.cast_succ :=
  by 
    cases i 
    simp only [Finₓ.append, Nat.not_lt_zeroₓ, Finₓ.nat_add_mk, add_lt_iff_neg_left, add_tsub_cancel_left, dif_neg,
      Finₓ.cast_succ_mk, not_false_iff, Finₓ.coe_mk]

theorem append_succ_nat_add_aux {s₁ s₂ : CompositionSeries X} (i : Finₓ s₂.length) :
  Finₓ.append (Nat.add_succ _ _).symm (s₁ ∘ Finₓ.castSucc) s₂ (Finₓ.natAdd s₁.length i).succ = s₂ i.succ :=
  by 
    cases' i with i hi 
    simp only [Finₓ.append, add_assocₓ, Nat.not_lt_zeroₓ, Finₓ.nat_add_mk, add_lt_iff_neg_left, add_tsub_cancel_left,
      Finₓ.succ_mk, dif_neg, not_false_iff, Finₓ.coe_mk]

/-- Append two composition series `s₁` and `s₂` such that
the least element of `s₁` is the maximum element of `s₂`. -/
@[simps length]
def append (s₁ s₂ : CompositionSeries X) (h : s₁.top = s₂.bot) : CompositionSeries X :=
  { length := s₁.length+s₂.length, series := Finₓ.append (Nat.add_succ _ _).symm (s₁ ∘ Finₓ.castSucc) s₂,
    step' :=
      fun i =>
        by 
          refine' Finₓ.addCases _ _ i
          ·
            intro i 
            rw [append_succ_cast_add_aux _ h, append_cast_add_aux]
            exact s₁.step i
          ·
            intro i 
            rw [append_nat_add_aux, append_succ_nat_add_aux]
            exact s₂.step i }

@[simp]
theorem append_cast_add {s₁ s₂ : CompositionSeries X} (h : s₁.top = s₂.bot) (i : Finₓ s₁.length) :
  append s₁ s₂ h (Finₓ.castAdd s₂.length i).cast_succ = s₁ i.cast_succ :=
  append_cast_add_aux i

@[simp]
theorem append_succ_cast_add {s₁ s₂ : CompositionSeries X} (h : s₁.top = s₂.bot) (i : Finₓ s₁.length) :
  append s₁ s₂ h (Finₓ.castAdd s₂.length i).succ = s₁ i.succ :=
  append_succ_cast_add_aux i h

@[simp]
theorem append_nat_add {s₁ s₂ : CompositionSeries X} (h : s₁.top = s₂.bot) (i : Finₓ s₂.length) :
  append s₁ s₂ h (Finₓ.natAdd s₁.length i).cast_succ = s₂ i.cast_succ :=
  append_nat_add_aux i

@[simp]
theorem append_succ_nat_add {s₁ s₂ : CompositionSeries X} (h : s₁.top = s₂.bot) (i : Finₓ s₂.length) :
  append s₁ s₂ h (Finₓ.natAdd s₁.length i).succ = s₂ i.succ :=
  append_succ_nat_add_aux i

/-- Add an element to the top of a `composition_series` -/
@[simps length]
def snoc (s : CompositionSeries X) (x : X) (hsat : is_maximal s.top x) : CompositionSeries X :=
  { length := s.length+1, series := Finₓ.snoc s x,
    step' :=
      fun i =>
        by 
          refine' Finₓ.lastCases _ _ i
          ·
            rwa [Finₓ.snoc_cast_succ, Finₓ.succ_last, Finₓ.snoc_last, ←top]
          ·
            intro i 
            rw [Finₓ.snoc_cast_succ, ←Finₓ.cast_succ_fin_succ, Finₓ.snoc_cast_succ]
            exact s.step _ }

@[simp]
theorem top_snoc (s : CompositionSeries X) (x : X) (hsat : is_maximal s.top x) : (snoc s x hsat).top = x :=
  Finₓ.snoc_last _ _

@[simp]
theorem snoc_last (s : CompositionSeries X) (x : X) (hsat : is_maximal s.top x) :
  snoc s x hsat (Finₓ.last (s.length+1)) = x :=
  Finₓ.snoc_last _ _

@[simp]
theorem snoc_cast_succ (s : CompositionSeries X) (x : X) (hsat : is_maximal s.top x) (i : Finₓ (s.length+1)) :
  snoc s x hsat i.cast_succ = s i :=
  Finₓ.snoc_cast_succ _ _ _

@[simp]
theorem bot_snoc (s : CompositionSeries X) (x : X) (hsat : is_maximal s.top x) : (snoc s x hsat).bot = s.bot :=
  by 
    rw [bot, bot, ←Finₓ.cast_succ_zero, snoc_cast_succ]

theorem mem_snoc {s : CompositionSeries X} {x y : X} {hsat : is_maximal s.top x} : y ∈ snoc s x hsat ↔ y ∈ s ∨ y = x :=
  by 
    simp only [snoc, mem_def]
    split 
    ·
      rintro ⟨i, rfl⟩
      refine' Finₓ.lastCases _ (fun i => _) i
      ·
        right 
        simp 
      ·
        left 
        simp 
    ·
      intro h 
      rcases h with (⟨i, rfl⟩ | rfl)
      ·
        use i.cast_succ 
        simp 
      ·
        use Finₓ.last _ 
        simp 

theorem eq_snoc_erase_top {s : CompositionSeries X} (h : 0 < s.length) :
  s = snoc (erase_top s) s.top (is_maximal_erase_top_top h) :=
  by 
    ext x 
    simp [mem_snoc, mem_erase_top h]
    byCases' h : x = s.top <;> simp [s.top_mem]

@[simp]
theorem snoc_erase_top_top {s : CompositionSeries X} (h : is_maximal s.erase_top.top s.top) :
  s.erase_top.snoc s.top h = s :=
  have h : 0 < s.length :=
    Nat.pos_of_ne_zeroₓ
      (by 
        intro hs 
        refine' ne_of_gtₓ (lt_of_is_maximal h) _ 
        simp [top, Finₓ.ext_iff, hs])
  (eq_snoc_erase_top h).symm

/-- Two `composition_series X`, `s₁` and `s₂` are equivalent if there is a bijection
`e : fin s₁.length ≃ fin s₂.length` such that for any `i`,
`iso (s₁ i) (s₁ i.succ) (s₂ (e i), s₂ (e i.succ))` -/
def equivalent (s₁ s₂ : CompositionSeries X) : Prop :=
  ∃ f : Finₓ s₁.length ≃ Finₓ s₂.length,
    ∀ (i : Finₓ s₁.length), iso (s₁ i.cast_succ, s₁ i.succ) (s₂ (f i).cast_succ, s₂ (f i).succ)

namespace Equivalent

@[refl]
theorem refl (s : CompositionSeries X) : equivalent s s :=
  ⟨Equiv.refl _, fun _ => (s.step _).iso_refl⟩

@[symm]
theorem symm {s₁ s₂ : CompositionSeries X} (h : equivalent s₁ s₂) : equivalent s₂ s₁ :=
  ⟨h.some.symm,
    fun i =>
      iso_symm
        (by 
          simpa using h.some_spec (h.some.symm i))⟩

@[trans]
theorem trans {s₁ s₂ s₃ : CompositionSeries X} (h₁ : equivalent s₁ s₂) (h₂ : equivalent s₂ s₃) : equivalent s₁ s₃ :=
  ⟨h₁.some.trans h₂.some, fun i => iso_trans (h₁.some_spec i) (h₂.some_spec (h₁.some i))⟩

theorem append {s₁ s₂ t₁ t₂ : CompositionSeries X} (hs : s₁.top = s₂.bot) (ht : t₁.top = t₂.bot) (h₁ : equivalent s₁ t₁)
  (h₂ : equivalent s₂ t₂) : equivalent (append s₁ s₂ hs) (append t₁ t₂ ht) :=
  let e : Finₓ (s₁.length+s₂.length) ≃ Finₓ (t₁.length+t₂.length) :=
    calc Finₓ (s₁.length+s₂.length) ≃ Sum (Finₓ s₁.length) (Finₓ s₂.length) := finSumFinEquiv.symm 
      _ ≃ Sum (Finₓ t₁.length) (Finₓ t₂.length) := Equiv.sumCongr h₁.some h₂.some 
      _ ≃ Finₓ (t₁.length+t₂.length) := finSumFinEquiv
      
  ⟨e,
    by 
      intro i 
      refine' Finₓ.addCases _ _ i
      ·
        intro i 
        simpa [top, bot] using h₁.some_spec i
      ·
        intro i 
        simpa [top, bot] using h₂.some_spec i⟩

protected theorem snoc {s₁ s₂ : CompositionSeries X} {x₁ x₂ : X} {hsat₁ : is_maximal s₁.top x₁}
  {hsat₂ : is_maximal s₂.top x₂} (hequiv : equivalent s₁ s₂) (htop : iso (s₁.top, x₁) (s₂.top, x₂)) :
  equivalent (s₁.snoc x₁ hsat₁) (s₂.snoc x₂ hsat₂) :=
  let e : Finₓ s₁.length.succ ≃ Finₓ s₂.length.succ :=
    calc Finₓ (s₁.length+1) ≃ Option (Finₓ s₁.length) := finSuccEquivLast 
      _ ≃ Option (Finₓ s₂.length) := Functor.mapEquiv Option hequiv.some 
      _ ≃ Finₓ (s₂.length+1) := finSuccEquivLast.symm
      
  ⟨e,
    fun i =>
      by 
        refine' Finₓ.lastCases _ _ i
        ·
          simpa [top] using htop
        ·
          intro i 
          simpa [Finₓ.succ_cast_succ] using hequiv.some_spec i⟩

theorem length_eq {s₁ s₂ : CompositionSeries X} (h : equivalent s₁ s₂) : s₁.length = s₂.length :=
  by 
    simpa using Fintype.card_congr h.some

theorem snoc_snoc_swap {s : CompositionSeries X} {x₁ x₂ y₁ y₂ : X} {hsat₁ : is_maximal s.top x₁}
  {hsat₂ : is_maximal s.top x₂} {hsaty₁ : is_maximal (snoc s x₁ hsat₁).top y₁}
  {hsaty₂ : is_maximal (snoc s x₂ hsat₂).top y₂} (hr₁ : iso (s.top, x₁) (x₂, y₂)) (hr₂ : iso (x₁, y₁) (s.top, x₂)) :
  equivalent (snoc (snoc s x₁ hsat₁) y₁ hsaty₁) (snoc (snoc s x₂ hsat₂) y₂ hsaty₂) :=
  let e : Finₓ ((s.length+1)+1) ≃ Finₓ ((s.length+1)+1) := Equiv.swap (Finₓ.last _) (Finₓ.castSucc (Finₓ.last _))
  have h1 : ∀ {i : Finₓ s.length}, i.cast_succ.cast_succ ≠ (Finₓ.last _).cast_succ :=
    fun _ =>
      ne_of_ltₓ
        (by 
          simp [Finₓ.cast_succ_lt_last])
  have h2 : ∀ {i : Finₓ s.length}, i.cast_succ.cast_succ ≠ Finₓ.last _ :=
    fun _ =>
      ne_of_ltₓ
        (by 
          simp [Finₓ.cast_succ_lt_last])
  ⟨e,
    by 
      intro i 
      dsimp only [e]
      refine' Finₓ.lastCases _ (fun i => _) i
      ·
        erw [Equiv.swap_apply_left, snoc_cast_succ, snoc_last, Finₓ.succ_last, snoc_last, snoc_cast_succ,
          snoc_cast_succ, Finₓ.succ_cast_succ, snoc_cast_succ, Finₓ.succ_last, snoc_last]
        exact hr₂
      ·
        refine' Finₓ.lastCases _ (fun i => _) i
        ·
          erw [Equiv.swap_apply_right, snoc_cast_succ, snoc_cast_succ, snoc_cast_succ, Finₓ.succ_cast_succ,
            snoc_cast_succ, Finₓ.succ_last, snoc_last, snoc_last, Finₓ.succ_last, snoc_last]
          exact hr₁
        ·
          erw [Equiv.swap_apply_of_ne_of_ne h2 h1, snoc_cast_succ, snoc_cast_succ, snoc_cast_succ, snoc_cast_succ,
            Finₓ.succ_cast_succ, snoc_cast_succ, Finₓ.succ_cast_succ, snoc_cast_succ, snoc_cast_succ, snoc_cast_succ]
          exact (s.step i).iso_refl⟩

end Equivalent

-- error in Order.JordanHolder: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero
{s₁ s₂ : composition_series X}
(hb : «expr = »(s₁.bot, s₂.bot))
(ht : «expr = »(s₁.top, s₂.top))
(hs₁ : «expr = »(s₁.length, 0)) : «expr = »(s₂.length, 0) :=
begin
  have [] [":", expr «expr = »(s₁.bot, s₁.top)] [],
  from [expr congr_arg s₁ (fin.ext (by simp [] [] [] ["[", expr hs₁, "]"] [] []))],
  have [] [":", expr «expr = »(fin.last s₂.length, (0 : fin s₂.length.succ))] [],
  from [expr s₂.injective (hb.symm.trans (this.trans ht)).symm],
  simpa [] [] [] ["[", expr fin.ext_iff, "]"] [] []
end

theorem length_pos_of_bot_eq_bot_of_top_eq_top_of_length_pos {s₁ s₂ : CompositionSeries X} (hb : s₁.bot = s₂.bot)
  (ht : s₁.top = s₂.top) : 0 < s₁.length → 0 < s₂.length :=
  not_imp_not.1
    (by 
      simp only [pos_iff_ne_zero, Ne.def, not_iff_not, not_not]
      exact length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero hb.symm ht.symm)

theorem eq_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero {s₁ s₂ : CompositionSeries X} (hb : s₁.bot = s₂.bot)
  (ht : s₁.top = s₂.top) (hs₁0 : s₁.length = 0) : s₁ = s₂ :=
  have  : ∀ x, x ∈ s₁ ↔ x = s₁.top :=
    fun x => ⟨fun hx => forall_mem_eq_of_length_eq_zero hs₁0 hx s₁.top_mem, fun hx => hx.symm ▸ s₁.top_mem⟩
  have  : ∀ x, x ∈ s₂ ↔ x = s₂.top :=
    fun x =>
      ⟨fun hx =>
          forall_mem_eq_of_length_eq_zero (length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero hb ht hs₁0) hx
            s₂.top_mem,
        fun hx => hx.symm ▸ s₂.top_mem⟩
  by 
    ext 
    simp 

-- error in Order.JordanHolder: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a `composition_series`, `s`, and an element `x`
such that `x` is maximal inside `s.top` there is a series, `t`,
such that `t.top = x`, `t.bot = s.bot`
and `snoc t s.top _` is equivalent to `s`. -/
theorem exists_top_eq_snoc_equivalant
(s : composition_series X)
(x : X)
(hm : is_maximal x s.top)
(hb : «expr ≤ »(s.bot, x)) : «expr∃ , »((t : composition_series X), «expr ∧ »(«expr = »(t.bot, s.bot), «expr ∧ »(«expr = »(«expr + »(t.length, 1), s.length), «expr∃ , »((htx : «expr = »(t.top, x)), equivalent s (snoc t s.top «expr ▸ »(htx.symm, hm)))))) :=
begin
  induction [expr hn, ":", expr s.length] [] ["with", ident n, ident ih] ["generalizing", ident s, ident x],
  { exact [expr (ne_of_gt (lt_of_le_of_lt hb (lt_of_is_maximal hm)) (forall_mem_eq_of_length_eq_zero hn s.top_mem s.bot_mem)).elim] },
  { have [ident h0s] [":", expr «expr < »(0, s.length)] [],
    from [expr «expr ▸ »(hn.symm, nat.succ_pos _)],
    by_cases [expr hetx, ":", expr «expr = »(s.erase_top.top, x)],
    { use [expr s.erase_top],
      simp [] [] [] ["[", "<-", expr hetx, ",", expr hn, "]"] [] [] },
    { have [ident imxs] [":", expr is_maximal «expr ⊓ »(x, s.erase_top.top) s.erase_top.top] [],
      from [expr is_maximal_of_eq_inf x s.top rfl (ne.symm hetx) hm (is_maximal_erase_top_top h0s)],
      have [] [] [":=", expr ih _ _ imxs (le_inf (by simpa [] [] [] [] [] []) (le_top_of_mem s.erase_top.bot_mem)) (by simp [] [] [] ["[", expr hn, "]"] [] [])],
      rcases [expr this, "with", "⟨", ident t, ",", ident htb, ",", ident htl, ",", ident htt, ",", ident hteqv, "⟩"],
      have [ident hmtx] [":", expr is_maximal t.top x] [],
      from [expr is_maximal_of_eq_inf s.erase_top.top s.top (by rw ["[", expr inf_comm, ",", expr htt, "]"] []) hetx (is_maximal_erase_top_top h0s) hm],
      use [expr snoc t x hmtx],
      refine [expr ⟨by simp [] [] [] ["[", expr htb, "]"] [] [], by simp [] [] [] ["[", expr htl, "]"] [] [], by simp [] [] [] [] [] [], _⟩],
      have [] [":", expr s.equivalent ((snoc t s.erase_top.top «expr ▸ »(htt.symm, imxs)).snoc s.top (by simpa [] [] [] [] [] ["using", expr is_maximal_erase_top_top h0s]))] [],
      { conv_lhs [] [] { rw [expr eq_snoc_erase_top h0s] },
        exact [expr equivalent.snoc hteqv (by simpa [] [] [] [] [] ["using", expr (is_maximal_erase_top_top h0s).iso_refl])] },
      refine [expr this.trans _],
      refine [expr equivalent.snoc_snoc_swap _ _],
      { exact [expr iso_symm (second_iso_of_eq hm (sup_eq_of_is_maximal hm (is_maximal_erase_top_top h0s) (ne.symm hetx)) htt.symm)] },
      { exact [expr second_iso_of_eq (is_maximal_erase_top_top h0s) (sup_eq_of_is_maximal (is_maximal_erase_top_top h0s) hm hetx) (by rw ["[", expr inf_comm, ",", expr htt, "]"] [])] } } }
end

-- error in Order.JordanHolder: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The **Jordan-Hölder** theorem, stated for any `jordan_holder_lattice`.
If two composition series start and finish at the same place, they are equivalent. -/
theorem jordan_holder
(s₁ s₂ : composition_series X)
(hb : «expr = »(s₁.bot, s₂.bot))
(ht : «expr = »(s₁.top, s₂.top)) : equivalent s₁ s₂ :=
begin
  induction [expr hle, ":", expr s₁.length] [] ["with", ident n, ident ih] ["generalizing", ident s₁, ident s₂],
  { rw ["[", expr eq_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero hb ht hle, "]"] [] },
  { have [ident h0s₂] [":", expr «expr < »(0, s₂.length)] [],
    from [expr length_pos_of_bot_eq_bot_of_top_eq_top_of_length_pos hb ht «expr ▸ »(hle.symm, nat.succ_pos _)],
    rcases [expr exists_top_eq_snoc_equivalant s₁ s₂.erase_top.top «expr ▸ »(ht.symm, is_maximal_erase_top_top h0s₂) «expr ▸ »(hb.symm, «expr ▸ »(s₂.bot_erase_top, bot_le_of_mem (top_mem _))), "with", "⟨", ident t, ",", ident htb, ",", ident htl, ",", ident htt, ",", ident hteq, "⟩"],
    have [] [] [":=", expr ih t s₂.erase_top (by simp [] [] [] ["[", expr htb, ",", "<-", expr hb, "]"] [] []) htt (nat.succ_inj'.1 (htl.trans hle))],
    refine [expr hteq.trans _],
    conv_rhs [] [] { rw ["[", expr eq_snoc_erase_top h0s₂, "]"] },
    simp [] [] ["only"] ["[", expr ht, "]"] [] [],
    exact [expr equivalent.snoc this (by simp [] [] [] ["[", expr htt, ",", expr (is_maximal_erase_top_top h0s₂).iso_refl, "]"] [] [])] }
end

end CompositionSeries

