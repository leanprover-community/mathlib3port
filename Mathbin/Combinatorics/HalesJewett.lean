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
structure line (α ι : Type _) where
  idxFun : ι → Option α
  proper : ∃ i, idx_fun i = none

namespace Line

instance α ι : CoeFun (Line α ι) fun _ => α → ι → α :=
  ⟨fun l x i => (l.idxFun i).getOrElse x⟩

/-- A line is monochromatic if all its points are the same color. -/
def is_mono {α ι κ} (C : (ι → α) → κ) (l : Line α ι) : Prop :=
  ∃ c, ∀ x, C (l x) = c

/-- The diagonal line. It is the identity at every coordinate. -/
def diagonal α ι [Nonempty ι] : Line α ι where
  idxFun := fun _ => none
  proper := ⟨Classical.arbitrary ι, rfl⟩

instance α ι [Nonempty ι] : Inhabited (Line α ι) :=
  ⟨diagonal α ι⟩

/-- The type of lines that are only one color except possibly at their endpoints. -/
structure almost_mono {α ι κ : Type _} (C : (ι → Option α) → κ) where
  line : Line (Option α) ι
  Color : κ
  has_color : ∀ x : α, C (line (some x)) = color

instance {α ι κ : Type _} [Nonempty ι] [Inhabited κ] : Inhabited (AlmostMono fun v : ι → Option α => (default : κ)) :=
  ⟨{ line := default, Color := default, has_color := fun _ => rfl }⟩

/-- The type of collections of lines such that
- each line is only one color except possibly at its endpoint
- the lines all have the same endpoint
- the colors of the lines are distinct.
Used in the proof `exists_mono_in_high_dimension`. -/
structure color_focused {α ι κ : Type _} (C : (ι → Option α) → κ) where
  lines : Multiset (AlmostMono C)
  focus : ι → Option α
  is_focused : ∀, ∀ p ∈ lines, ∀, AlmostMono.line p none = focus
  distinct_colors : (lines.map AlmostMono.color).Nodup

instance {α ι κ} (C : (ι → Option α) → κ) : Inhabited (ColorFocused C) :=
  ⟨⟨0, fun _ => none, fun _ => False.elim, Multiset.nodup_zero⟩⟩

/-- A function `f : α → α'` determines a function `line α ι → line α' ι`. For a coordinate `i`,
`l.map f` is the identity at `i` if `l` is, and constantly `f y` if `l` is constantly `y` at `i`. -/
def map {α α' ι} (f : α → α') (l : Line α ι) : Line α' ι where
  idxFun := fun i => (l.idxFun i).map f
  proper :=
    ⟨l.proper.some, by
      rw [l.proper.some_spec, Option.map_none'ₓ]⟩

/-- A point in `ι → α` and a line in `ι' → α` determine a line in `ι ⊕ ι' → α`. -/
def vertical {α ι ι'} (v : ι → α) (l : Line α ι') : Line α (Sum ι ι') where
  idxFun := Sum.elim (some ∘ v) l.idxFun
  proper := ⟨Sum.inr l.proper.some, l.proper.some_spec⟩

/-- A line in `ι → α` and a point in `ι' → α` determine a line in `ι ⊕ ι' → α`. -/
def horizontal {α ι ι'} (l : Line α ι) (v : ι' → α) : Line α (Sum ι ι') where
  idxFun := Sum.elim l.idxFun (some ∘ v)
  proper := ⟨Sum.inl l.proper.some, l.proper.some_spec⟩

/-- One line in `ι → α` and one in `ι' → α` together determine a line in `ι ⊕ ι' → α`. -/
def Prod {α ι ι'} (l : Line α ι) (l' : Line α ι') : Line α (Sum ι ι') where
  idxFun := Sum.elim l.idxFun l'.idxFun
  proper := ⟨Sum.inl l.proper.some, l.proper.some_spec⟩

theorem apply {α ι} (l : Line α ι) (x : α) : l x = fun i => (l.idxFun i).getOrElse x :=
  rfl

theorem apply_none {α ι} (l : Line α ι) (x : α) (i : ι) (h : l.idxFun i = none) : l x i = x := by
  simp only [Option.get_or_else_none, h, l.apply]

theorem apply_of_ne_none {α ι} (l : Line α ι) (x : α) (i : ι) (h : l.idxFun i ≠ none) : some (l x i) = l.idxFun i := by
  rw [l.apply, Option.get_or_else_of_ne_none h]

@[simp]
theorem map_apply {α α' ι} (f : α → α') (l : Line α ι) (x : α) : l.map f (f x) = f ∘ l x := by
  simp only [line.apply, line.map, Option.get_or_else_map]

@[simp]
theorem vertical_apply {α ι ι'} (v : ι → α) (l : Line α ι') (x : α) : l.vertical v x = Sum.elim v (l x) := by
  funext i
  cases i <;> rfl

@[simp]
theorem horizontal_apply {α ι ι'} (l : Line α ι) (v : ι' → α) (x : α) : l.horizontal v x = Sum.elim (l x) v := by
  funext i
  cases i <;> rfl

@[simp]
theorem prod_apply {α ι ι'} (l : Line α ι) (l' : Line α ι') (x : α) : l.Prod l' x = Sum.elim (l x) (l' x) := by
  funext i
  cases i <;> rfl

@[simp]
theorem diagonal_apply {α ι} [Nonempty ι] (x : α) : Line.diagonal α ι x = fun i => x := by
  simp_rw [line.apply, line.diagonal, Option.get_or_else_none]

/-- The Hales-Jewett theorem. This version has a restriction on universe levels which is necessary
for the proof. See `exists_mono_in_high_dimension` for a fully universe-polymorphic version. -/
private theorem exists_mono_in_high_dimension' :
    ∀ α : Type u [Fintype α] κ : Type max v u [Fintype κ],
      ∃ (ι : Type)(_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Line α ι, l.IsMono C :=
  Fintype.induction_empty_option
    (fun α α' e =>
      forall_imp fun κ =>
        forall_imp fun _ =>
          Exists.impₓ fun ι =>
            Exists.impₓ fun _ h C =>
              let ⟨l, c, lc⟩ := h fun v => C (e ∘ v)
              ⟨l.map e, c,
                e.forall_congr_left.mp fun x => by
                  rw [← lc x, line.map_apply]⟩)
    (by
      intros κ _
      by_cases' h : Nonempty κ
      · skip
        exact ⟨Unit, inferInstance, fun C => ⟨default, Classical.arbitrary _, Pempty.rec _⟩⟩
        
      · exact ⟨Empty, inferInstance, fun C => (h ⟨C (Empty.rec _)⟩).elim⟩
        )
    (by
      intros α _ ihα κ _
      by_cases' h : Nonempty α
      on_goal 1 =>
        refine' ⟨Unit, inferInstance, fun C => ⟨diagonal _ _, C fun _ => none, _⟩⟩
        rintro (_ | ⟨a⟩)
        rfl
        exact (h ⟨a⟩).elim
      suffices key :
        ∀ r : ℕ,
          ∃ (ι : Type)(_ : Fintype ι),
            ∀ C : (ι → Option α) → κ, (∃ s : color_focused C, s.lines.card = r) ∨ ∃ l, is_mono C l
      · obtain ⟨ι, _inst, hι⟩ := key (Fintype.card κ + 1)
        refine' ⟨ι, _inst, fun C => (hι C).resolve_left _⟩
        rintro ⟨s, sr⟩
        apply Nat.not_succ_le_selfₓ (Fintype.card κ)
        rw [← Nat.add_one, ← sr, ← Multiset.card_map, ← Finset.card_mk]
        exact Finset.card_le_univ ⟨_, s.distinct_colors⟩
        
      intro r
      induction' r with r ihr
      · exact ⟨Empty, inferInstance, fun C => Or.inl ⟨default, Multiset.card_zero⟩⟩
        
      obtain ⟨ι, _inst, hι⟩ := ihr
      skip
      specialize ihα ((ι → Option α) → κ)
      obtain ⟨ι', _inst, hι'⟩ := ihα
      skip
      refine' ⟨Sum ι ι', inferInstance, _⟩
      intro C
      specialize hι' fun v' v => C (Sum.elim v (some ∘ v'))
      obtain ⟨l', C', hl'⟩ := hι'
      have mono_of_mono : (∃ l, is_mono C' l) → ∃ l, is_mono C l := by
        rintro ⟨l, c, hl⟩
        refine' ⟨l.horizontal (some ∘ l' (Classical.arbitrary α)), c, fun x => _⟩
        rw [line.horizontal_apply, ← hl, ← hl']
      specialize hι C'
      rcases hι with (⟨s, sr⟩ | _)
      on_goal 1 =>
        exact Or.inr (mono_of_mono hι)
      by_cases' h : ∃ p ∈ s.lines, (p : almost_mono _).Color = C' s.focus
      · obtain ⟨p, p_mem, hp⟩ := h
        refine' Or.inr (mono_of_mono ⟨p.line, p.color, _⟩)
        rintro (_ | _)
        rw [hp, s.is_focused p p_mem]
        apply p.has_color
        
      refine'
        Or.inl
          ⟨⟨(s.lines.map _).cons ⟨(l'.map some).vertical s.focus, C' s.focus, fun x => _⟩,
              Sum.elim s.focus (l'.map some none), _, _⟩,
            _⟩
      · rw [vertical_apply, ← congr_funₓ (hl' x), line.map_apply]
        
      · refine' fun p => ⟨p.line.prod (l'.map some), p.Color, fun x => _⟩
        rw [line.prod_apply, line.map_apply, ← p.has_color, ← congr_funₓ (hl' x)]
        
      · simp_rw [Multiset.mem_cons, Multiset.mem_map]
        rintro _ (rfl | ⟨q, hq, rfl⟩)
        · rw [line.vertical_apply]
          
        · rw [line.prod_apply, s.is_focused q hq]
          
        
      · rw [Multiset.map_cons, Multiset.map_map, Multiset.nodup_cons, Multiset.mem_map]
        exact ⟨fun ⟨q, hq, he⟩ => h ⟨q, hq, he⟩, s.distinct_colors⟩
        
      · rw [Multiset.card_cons, Multiset.card_map, sr]
        )

/-- The Hales-Jewett theorem: for any finite types `α` and `κ`, there exists a finite type `ι` such
that whenever the hypercube `ι → α` is `κ`-colored, there is a monochromatic combinatorial line. -/
theorem exists_mono_in_high_dimension (α : Type u) [Fintype α] (κ : Type v) [Fintype κ] :
    ∃ (ι : Type)(_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Line α ι, l.IsMono C :=
  let ⟨ι, ιfin, hι⟩ := exists_mono_in_high_dimension' α (Ulift κ)
  ⟨ι, ιfin, fun C =>
    let ⟨l, c, hc⟩ := hι (Ulift.up ∘ C)
    ⟨l, c.down, fun x => by
      rw [← hc]⟩⟩

end Line

/-- A generalization of Van der Waerden's theorem: if `M` is a finitely colored commutative
monoid, and `S` is a finite subset, then there exists a monochromatic homothetic copy of `S`. -/
theorem exists_mono_homothetic_copy {M κ} [AddCommMonoidₓ M] (S : Finset M) [Fintype κ] (C : M → κ) :
    ∃ a > 0, ∃ (b : M)(c : κ), ∀, ∀ s ∈ S, ∀, C (a • s + b) = c := by
  obtain ⟨ι, _inst, hι⟩ := line.exists_mono_in_high_dimension S κ
  skip
  specialize hι fun v => C <| ∑ i, v i
  obtain ⟨l, c, hl⟩ := hι
  set s : Finset ι := { i ∈ Finset.univ | l.idx_fun i = none } with hs
  refine' ⟨s.card, finset.card_pos.mpr ⟨l.proper.some, _⟩, ∑ i in sᶜ, ((l.idx_fun i).map coe).getOrElse 0, c, _⟩
  · rw [hs, Finset.sep_def, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, l.proper.some_spec⟩
    
  intro x xs
  rw [← hl ⟨x, xs⟩]
  clear hl
  congr
  rw [← Finset.sum_add_sum_compl s]
  congr 1
  · rw [← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hs, Finset.sep_def, Finset.mem_filter] at hi
    rw [l.apply_none _ _ hi.right, Subtype.coe_mk]
    
  · apply Finset.sum_congr rfl
    intro i hi
    rw [hs, Finset.sep_def, Finset.compl_filter, Finset.mem_filter] at hi
    obtain ⟨y, hy⟩ := option.ne_none_iff_exists.mp hi.right
    simp_rw [line.apply, ← hy, Option.map_some'ₓ, Option.get_or_else_some]
    

end Combinatorics

