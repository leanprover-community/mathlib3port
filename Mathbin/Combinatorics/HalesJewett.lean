import Mathbin.Data.Fintype.Basic 
import Mathbin.Algebra.BigOperators.Basic

/-!
# The Hales-Jewett theorem

We prove the Hales-Jewett theorem and deduce Van der Waerden's theorem as a corollary.

The Hales-Jewett theorem is a result in Ramsey theory dealing with *combinatorial lines*. Given
an 'alphabet' `α : Type*` and `a b : α`, an example of a combinatorial line in `α^5` is
`{ (a, x, x, b, x) | x : α }`. See `combinatorics.line` for a precise general definition. The
Hales-Jewett theorem states that for any fixed finite types `α` and `κ`, there exists a (potentially
huge) finite type `ι` such that whenever `ι → α` is `κ`-colored (i.e. for any coloring
`C : (ι → α) → κ`), there exists a monochromatic line. We prove the Hales-Jewett theorem using
the idea of *color focusing* and a *product argument*. See the proof of
`combinatorics.line.exists_mono_in_high_dimension'` for details.

The version of Van der Waerden's theorem in this file states that whenever a commutative monoid `M`
is finitely colored and `S` is a finite subset, there exists a monochromatic homothetic copy of `S`.
This follows from the Hales-Jewett theorem by considering the map `(ι → S) → M` sending `v`
to `∑ i : ι, v i`, which sends a combinatorial line to a homothetic copy of `S`.

## Main results

- `combinatorics.line.exists_mono_in_high_dimension`: the Hales-Jewett theorem.
- `combinatorics.exists_mono_homothetic_copy`: a generalization of Van der Waerden's theorem.

## Implementation details

For convenience, we work directly with finite types instead of natural numbers. That is, we write
`α, ι, κ` for (finite) types where one might traditionally use natural numbers `n, H, c`. This
allows us to work directly with `α`, `option α`, `(ι → α) → κ`, and `ι ⊕ ι'` instead of `fin n`,
`fin (n+1)`, `fin (c^(n^H))`, and `fin (H + H')`.

## Todo

- Prove a finitary version of Van der Waerden's theorem (either by compactness or by modifying the
current proof).

- One could reformulate the proof of Hales-Jewett to give explicit upper bounds on the number of
coordinates needed.

## Tags

combinatorial line, Ramsey theory, arithmetic progession

### References

* https://en.wikipedia.org/wiki/Hales%E2%80%93Jewett_theorem

-/


open_locale Classical

open_locale BigOperators

universe u v

namespace Combinatorics

/-- The type of combinatorial lines. A line `l : line α ι` in the hypercube `ι → α` defines a
function `α → ι → α` from `α` to the hypercube, such that for each coordinate `i : ι`, the function
`λ x, l x i` is either `id` or constant. We require lines to be nontrivial in the sense that
`λ x, l x i` is `id` for at least one `i`.

Formally, a line is represented by the function `l.idx_fun : ι → option α` which says whether
`λ x, l x i` is `id` (corresponding to `l.idx_fun i = none`) or constantly `y` (corresponding to
`l.idx_fun i = some y`).

When `α` has size `1` there can be many elements of `line α ι` defining the same function. -/
structure line(α ι : Type _) where 
  idxFun : ι → Option α 
  proper : ∃ i, idx_fun i = none

namespace Line

instance  α ι : CoeFun (line α ι) fun _ => α → ι → α :=
  ⟨fun l x i => (l.idx_fun i).getOrElse x⟩

/-- A line is monochromatic if all its points are the same color. -/
def is_mono {α ι κ} (C : (ι → α) → κ) (l : line α ι) : Prop :=
  ∃ c, ∀ x, C (l x) = c

/-- The diagonal line. It is the identity at every coordinate. -/
def diagonal α ι [Nonempty ι] : line α ι :=
  { idxFun := fun _ => none, proper := ⟨Classical.arbitrary ι, rfl⟩ }

instance  α ι [Nonempty ι] : Inhabited (line α ι) :=
  ⟨diagonal α ι⟩

/-- The type of lines that are only one color except possibly at their endpoints. -/
structure almost_mono{α ι κ : Type _}(C : (ι → Option α) → κ) where 
  line : line (Option α) ι 
  Color : κ 
  has_color : ∀ x : α, C (line (some x)) = color

instance  {α ι κ : Type _} [Nonempty ι] [Inhabited κ] : Inhabited (almost_mono fun v : ι → Option α => default κ) :=
  ⟨{ line := default _, Color := default κ, has_color := fun _ => rfl }⟩

/-- The type of collections of lines such that
- each line is only one color except possibly at its endpoint
- the lines all have the same endpoint
- the colors of the lines are distinct.
Used in the proof `exists_mono_in_high_dimension`. -/
structure color_focused{α ι κ : Type _}(C : (ι → Option α) → κ) where 
  lines : Multiset (almost_mono C)
  focus : ι → Option α 
  is_focused : ∀ p _ : p ∈ lines, almost_mono.line p none = focus 
  distinct_colors : (lines.map almost_mono.color).Nodup

instance  {α ι κ} (C : (ι → Option α) → κ) : Inhabited (color_focused C) :=
  ⟨⟨0, fun _ => none, fun _ => False.elim, Multiset.nodup_zero⟩⟩

/-- A function `f : α → α'` determines a function `line α ι → line α' ι`. For a coordinate `i`,
`l.map f` is the identity at `i` if `l` is, and constantly `f y` if `l` is constantly `y` at `i`. -/
def map {α α' ι} (f : α → α') (l : line α ι) : line α' ι :=
  { idxFun := fun i => (l.idx_fun i).map f,
    proper :=
      ⟨l.proper.some,
        by 
          rw [l.proper.some_spec, Option.map_none']⟩ }

/-- A point in `ι → α` and a line in `ι' → α` determine a line in `ι ⊕ ι' → α`. -/
def vertical {α ι ι'} (v : ι → α) (l : line α ι') : line α (Sum ι ι') :=
  { idxFun := Sum.elim (some ∘ v) l.idx_fun, proper := ⟨Sum.inr l.proper.some, l.proper.some_spec⟩ }

/-- A line in `ι → α` and a point in `ι' → α` determine a line in `ι ⊕ ι' → α`. -/
def horizontal {α ι ι'} (l : line α ι) (v : ι' → α) : line α (Sum ι ι') :=
  { idxFun := Sum.elim l.idx_fun (some ∘ v), proper := ⟨Sum.inl l.proper.some, l.proper.some_spec⟩ }

/-- One line in `ι → α` and one in `ι' → α` together determine a line in `ι ⊕ ι' → α`. -/
def Prod {α ι ι'} (l : line α ι) (l' : line α ι') : line α (Sum ι ι') :=
  { idxFun := Sum.elim l.idx_fun l'.idx_fun, proper := ⟨Sum.inl l.proper.some, l.proper.some_spec⟩ }

theorem apply {α ι} (l : line α ι) (x : α) : l x = fun i => (l.idx_fun i).getOrElse x :=
  rfl

theorem apply_none {α ι} (l : line α ι) (x : α) (i : ι) (h : l.idx_fun i = none) : l x i = x :=
  by 
    simp only [Option.get_or_else_none, h, l.apply]

theorem apply_of_ne_none {α ι} (l : line α ι) (x : α) (i : ι) (h : l.idx_fun i ≠ none) : some (l x i) = l.idx_fun i :=
  by 
    rw [l.apply, Option.get_or_else_of_ne_none h]

@[simp]
theorem map_apply {α α' ι} (f : α → α') (l : line α ι) (x : α) : l.map f (f x) = f ∘ l x :=
  by 
    simp only [line.apply, line.map, Option.get_or_else_map]

@[simp]
theorem vertical_apply {α ι ι'} (v : ι → α) (l : line α ι') (x : α) : l.vertical v x = Sum.elim v (l x) :=
  by 
    funext i 
    cases i <;> rfl

@[simp]
theorem horizontal_apply {α ι ι'} (l : line α ι) (v : ι' → α) (x : α) : l.horizontal v x = Sum.elim (l x) v :=
  by 
    funext i 
    cases i <;> rfl

@[simp]
theorem prod_apply {α ι ι'} (l : line α ι) (l' : line α ι') (x : α) : l.prod l' x = Sum.elim (l x) (l' x) :=
  by 
    funext i 
    cases i <;> rfl

@[simp]
theorem diagonal_apply {α ι} [Nonempty ι] (x : α) : line.diagonal α ι x = fun i => x :=
  by 
    simpRw [line.apply, line.diagonal, Option.get_or_else_none]

-- error in Combinatorics.HalesJewett: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Hales-Jewett theorem. This version has a restriction on universe levels which is necessary
for the proof. See `exists_mono_in_high_dimension` for a fully universe-polymorphic version. -/
private
theorem exists_mono_in_high_dimension' : ∀
(α : Type u)
[fintype α]
(κ : Type max v u)
[fintype κ], «expr∃ , »((ι : Type) (_ : fintype ι), ∀ C : (ι → α) → κ, «expr∃ , »((l : line α ι), l.is_mono C)) :=
fintype.induction_empty_option (λ
 α
 α'
 e, «expr $ »(forall_imp, λ
  κ, «expr $ »(forall_imp, λ
   _, «expr $ »(Exists.imp, λ
    ι, «expr $ »(Exists.imp, λ _ h C, let ⟨l, c, lc⟩ := h (λ v, C «expr ∘ »(e, v)) in
     ⟨l.map e, c, «expr $ »(e.forall_congr_left.mp, λ
       x, by rw ["[", "<-", expr lc x, ",", expr line.map_apply, "]"] [])⟩))))) (begin
   introsI [ident κ, "_"],
   by_cases [expr h, ":", expr nonempty κ],
   { resetI,
     exact [expr ⟨unit, infer_instance, λ C, ⟨default _, classical.arbitrary _, pempty.rec _⟩⟩] },
   { exact [expr ⟨empty, infer_instance, λ C, (h ⟨C (empty.rec _)⟩).elim⟩] }
 end) (begin
   introsI [ident α, "_", ident ihα, ident κ, "_"],
   by_cases [expr h, ":", expr nonempty α],
   work_on_goal [1] { refine [expr ⟨unit, infer_instance, λ C, ⟨diagonal _ _, C (λ _, none), _⟩⟩],
     rintros ["(", "_", "|", "⟨", ident a, "⟩", ")"],
     refl,
     exact [expr (h ⟨a⟩).elim] },
   suffices [ident key] [":", expr ∀
    r : exprℕ(), «expr∃ , »((ι : Type)
     (_ : fintype ι), ∀
     C : (ι → option α) → κ, «expr ∨ »(«expr∃ , »((s : color_focused C), «expr = »(s.lines.card, r)), «expr∃ , »((l), is_mono C l)))],
   { obtain ["⟨", ident ι, ",", ident _inst, ",", ident hι, "⟩", ":=", expr key «expr + »(fintype.card κ, 1)],
     refine [expr ⟨ι, _inst, λ C, (hι C).resolve_left _⟩],
     rintro ["⟨", ident s, ",", ident sr, "⟩"],
     apply [expr nat.not_succ_le_self (fintype.card κ)],
     rw ["[", "<-", expr nat.add_one, ",", "<-", expr sr, ",", "<-", expr multiset.card_map, ",", "<-", expr finset.card_mk, "]"] [],
     exact [expr finset.card_le_univ ⟨_, s.distinct_colors⟩] },
   intro [ident r],
   induction [expr r] [] ["with", ident r, ident ihr] [],
   { exact [expr ⟨empty, infer_instance, λ C, or.inl ⟨default _, multiset.card_zero⟩⟩] },
   obtain ["⟨", ident ι, ",", ident _inst, ",", ident hι, "⟩", ":=", expr ihr],
   resetI,
   specialize [expr ihα ((ι → option α) → κ)],
   obtain ["⟨", ident ι', ",", ident _inst, ",", ident hι', "⟩", ":=", expr ihα],
   resetI,
   refine [expr ⟨«expr ⊕ »(ι, ι'), infer_instance, _⟩],
   intro [ident C],
   specialize [expr hι' (λ v' v, C (sum.elim v «expr ∘ »(some, v')))],
   obtain ["⟨", ident l', ",", ident C', ",", ident hl', "⟩", ":=", expr hι'],
   have [ident mono_of_mono] [":", expr «expr∃ , »((l), is_mono C' l) → «expr∃ , »((l), is_mono C l)] [],
   { rintro ["⟨", ident l, ",", ident c, ",", ident hl, "⟩"],
     refine [expr ⟨l.horizontal «expr ∘ »(some, l' (classical.arbitrary α)), c, λ x, _⟩],
     rw ["[", expr line.horizontal_apply, ",", "<-", expr hl, ",", "<-", expr hl', "]"] [] },
   specialize [expr hι C'],
   rcases [expr hι, "with", "⟨", ident s, ",", ident sr, "⟩", "|", "_"],
   work_on_goal [1] { exact [expr or.inr (mono_of_mono hι)] },
   by_cases [expr h, ":", expr «expr∃ , »((p «expr ∈ » s.lines), «expr = »((p : almost_mono _).color, C' s.focus))],
   { obtain ["⟨", ident p, ",", ident p_mem, ",", ident hp, "⟩", ":=", expr h],
     refine [expr or.inr (mono_of_mono ⟨p.line, p.color, _⟩)],
     rintro ["(", "_", "|", "_", ")"],
     rw ["[", expr hp, ",", expr s.is_focused p p_mem, "]"] [],
     apply [expr p.has_color] },
   refine [expr or.inl ⟨⟨(s.lines.map _).cons ⟨(l'.map some).vertical s.focus, C' s.focus, λ
       x, _⟩, sum.elim s.focus (l'.map some none), _, _⟩, _⟩],
   { rw ["[", expr vertical_apply, ",", "<-", expr congr_fun (hl' x), ",", expr line.map_apply, "]"] [] },
   { refine [expr λ p, ⟨p.line.prod (l'.map some), p.color, λ x, _⟩],
     rw ["[", expr line.prod_apply, ",", expr line.map_apply, ",", "<-", expr p.has_color, ",", "<-", expr congr_fun (hl' x), "]"] [] },
   { simp_rw ["[", expr multiset.mem_cons, ",", expr multiset.mem_map, "]"] [],
     rintros ["_", "(", ident rfl, "|", "⟨", ident q, ",", ident hq, ",", ident rfl, "⟩", ")"],
     { rw [expr line.vertical_apply] [] },
     { rw ["[", expr line.prod_apply, ",", expr s.is_focused q hq, "]"] [] } },
   { rw ["[", expr multiset.map_cons, ",", expr multiset.map_map, ",", expr multiset.nodup_cons, ",", expr multiset.mem_map, "]"] [],
     exact [expr ⟨λ ⟨q, hq, he⟩, h ⟨q, hq, he⟩, s.distinct_colors⟩] },
   { rw ["[", expr multiset.card_cons, ",", expr multiset.card_map, ",", expr sr, "]"] [] }
 end)

/-- The Hales-Jewett theorem: for any finite types `α` and `κ`, there exists a finite type `ι` such
that whenever the hypercube `ι → α` is `κ`-colored, there is a monochromatic combinatorial line. -/
theorem exists_mono_in_high_dimension (α : Type u) [Fintype α] (κ : Type v) [Fintype κ] :
  ∃ (ι : Type)(_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : line α ι, l.is_mono C :=
  let ⟨ι, ιfin, hι⟩ := exists_mono_in_high_dimension' α (Ulift κ)
  ⟨ι, ιfin,
    fun C =>
      let ⟨l, c, hc⟩ := hι (Ulift.up ∘ C)
      ⟨l, c.down,
        fun x =>
          by 
            rw [←hc]⟩⟩

end Line

/-- A generalization of Van der Waerden's theorem: if `M` is a finitely colored commutative
monoid, and `S` is a finite subset, then there exists a monochromatic homothetic copy of `S`. -/
theorem exists_mono_homothetic_copy {M κ} [AddCommMonoidₓ M] (S : Finset M) [Fintype κ] (C : M → κ) :
  ∃ (a : _)(_ : a > 0)(b : M)(c : κ), ∀ s _ : s ∈ S, C ((a • s)+b) = c :=
  by 
    obtain ⟨ι, _inst, hι⟩ := line.exists_mono_in_high_dimension S κ 
    skip 
    specialize hι fun v => C$ ∑i, v i 
    obtain ⟨l, c, hl⟩ := hι 
    set s : Finset ι := { i∈Finset.univ | l.idx_fun i = none } with hs 
    refine'
      ⟨s.card, finset.card_pos.mpr ⟨l.proper.some, _⟩, ∑i in «expr ᶜ» s, ((l.idx_fun i).map coeₓ).getOrElse 0, c, _⟩
    ·
      rw [hs, Finset.sep_def, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, l.proper.some_spec⟩
    intro x xs 
    rw [←hl ⟨x, xs⟩]
    clear hl 
    congr 
    rw [←Finset.sum_add_sum_compl s]
    congr 1
    ·
      rw [←Finset.sum_const]
      apply Finset.sum_congr rfl 
      intro i hi 
      rw [hs, Finset.sep_def, Finset.mem_filter] at hi 
      rw [l.apply_none _ _ hi.right, Subtype.coe_mk]
    ·
      apply Finset.sum_congr rfl 
      intro i hi 
      rw [hs, Finset.sep_def, Finset.compl_filter, Finset.mem_filter] at hi 
      obtain ⟨y, hy⟩ := option.ne_none_iff_exists.mp hi.right 
      simpRw [line.apply, ←hy, Option.map_some', Option.get_or_else_some]

end Combinatorics

