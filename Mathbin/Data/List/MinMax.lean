import Mathbin.Data.List.Basic

/-!
# Minimum and maximum of lists

## Main definitions

The main definitions are `argmax`, `argmin`, `minimum` and `maximum` for lists.

`argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such that
  `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
  `argmax f []` = none`

`minimum l` returns an `with_top α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`
-/


namespace List

variable {α : Type _} {β : Type _} [LinearOrderₓ β]

/-- Auxiliary definition to define `argmax` -/
def argmax₂ (f : α → β) (a : Option α) (b : α) : Option α :=
  Option.casesOn a (some b) fun c => if f b ≤ f c then some c else some b

/-- `argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such
that `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
`argmax f []` = none` -/
def argmax (f : α → β) (l : List α) : Option α :=
  l.foldl (argmax₂ f) none

/-- `argmin f l` returns `some a`, where `a` of `l` that minimises `f a`. If there are `a b` such
that `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
`argmin f []` = none` -/
def argmin (f : α → β) (l : List α) :=
  @argmax _ (OrderDual β) _ f l

@[simp]
theorem argmax_two_self (f : α → β) (a : α) : argmax₂ f (some a) a = a :=
  if_pos (le_reflₓ _)

@[simp]
theorem argmax_nil (f : α → β) : argmax f [] = none :=
  rfl

@[simp]
theorem argmin_nil (f : α → β) : argmin f [] = none :=
  rfl

@[simp]
theorem argmax_singleton {f : α → β} {a : α} : argmax f [a] = some a :=
  rfl

@[simp]
theorem argmin_singleton {f : α → β} {a : α} : argmin f [a] = a :=
  rfl

@[simp]
theorem foldl_argmax₂_eq_none {f : α → β} {l : List α} {o : Option α} :
  l.foldl (argmax₂ f) o = none ↔ l = [] ∧ o = none :=
  List.reverseRecOn l
      (by 
        simp )$
    fun tl hd =>
      by 
        simp [argmax₂] <;>
          cases foldl (argmax₂ f) o tl <;>
            simp  <;>
              try 
                  splitIfs <;>
                simp 

-- error in Data.List.MinMax: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem le_of_foldl_argmax₂
{f : α → β}
{l} : ∀ {a m : α} {o : option α}, «expr ∈ »(a, l) → «expr ∈ »(m, foldl (argmax₂ f) o l) → «expr ≤ »(f a, f m) :=
list.reverse_rec_on l (λ
 _
 _
 _
 h, «expr $ »(absurd h, not_mem_nil _)) (begin
   intros [ident tl, "_", ident ih, "_", "_", "_", ident h, ident ho],
   rw ["[", expr foldl_append, ",", expr foldl_cons, ",", expr foldl_nil, ",", expr argmax₂, "]"] ["at", ident ho],
   cases [expr hf, ":", expr foldl (argmax₂ f) o tl] [],
   { rw ["[", expr hf, "]"] ["at", ident ho],
     rw ["[", expr foldl_argmax₂_eq_none, "]"] ["at", ident hf],
     simp [] [] [] ["[", expr hf.1, ",", expr hf.2, ",", "*", "]"] [] ["at", "*"] },
   rw ["[", expr hf, ",", expr option.mem_def, "]"] ["at", ident ho],
   dsimp ["only"] [] [] ["at", ident ho],
   cases [expr mem_append.1 h] ["with", ident h, ident h],
   { refine [expr le_trans (ih h hf) _],
     have [] [] [":=", expr @le_of_lt _ _ (f val) (f m)],
     split_ifs ["at", ident ho] []; simp [] [] [] ["*"] [] ["at", "*"] },
   { split_ifs ["at", ident ho] []; simp [] [] [] ["*"] [] ["at", "*"] }
 end)

-- error in Data.List.MinMax: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem foldl_argmax₂_mem
(f : α → β)
(l) : ∀ a m : α, «expr ∈ »(m, foldl (argmax₂ f) (some a) l) → «expr ∈ »(m, «expr :: »(a, l)) :=
list.reverse_rec_on l (by simp [] [] [] ["[", expr eq_comm, "]"] [] []) (begin
   assume [binders (tl hd ih a m)],
   simp [] [] ["only"] ["[", expr foldl_append, ",", expr foldl_cons, ",", expr foldl_nil, ",", expr argmax₂, "]"] [] [],
   cases [expr hf, ":", expr foldl (argmax₂ f) (some a) tl] [],
   { simp [] [] [] [] [] [] { contextual := tt } },
   { dsimp ["only"] [] [] [],
     split_ifs [] [],
     { finish ["[", expr ih _ _ hf, "]"] [] },
     { simp [] [] [] [] [] [] { contextual := tt } } }
 end)

theorem argmax_mem {f : α → β} : ∀ {l : List α} {m : α}, m ∈ argmax f l → m ∈ l
| [], m =>
  by 
    simp 
| hd :: tl, m =>
  by 
    simpa [argmax, argmax₂] using foldl_argmax₂_mem f tl hd m

theorem argmin_mem {f : α → β} : ∀ {l : List α} {m : α}, m ∈ argmin f l → m ∈ l :=
  @argmax_mem _ (OrderDual β) _ _

@[simp]
theorem argmax_eq_none {f : α → β} {l : List α} : l.argmax f = none ↔ l = [] :=
  by 
    simp [argmax]

@[simp]
theorem argmin_eq_none {f : α → β} {l : List α} : l.argmin f = none ↔ l = [] :=
  @argmax_eq_none _ (OrderDual β) _ _ _

theorem le_argmax_of_mem {f : α → β} {a m : α} {l : List α} : a ∈ l → m ∈ argmax f l → f a ≤ f m :=
  le_of_foldl_argmax₂

theorem argmin_le_of_mem {f : α → β} {a m : α} {l : List α} : a ∈ l → m ∈ argmin f l → f m ≤ f a :=
  @le_argmax_of_mem _ (OrderDual β) _ _ _ _ _

theorem argmax_concat (f : α → β) (a : α) (l : List α) :
  argmax f (l ++ [a]) = Option.casesOn (argmax f l) (some a) fun c => if f a ≤ f c then some c else some a :=
  by 
    rw [argmax, argmax] <;> simp [argmax₂]

theorem argmin_concat (f : α → β) (a : α) (l : List α) :
  argmin f (l ++ [a]) = Option.casesOn (argmin f l) (some a) fun c => if f c ≤ f a then some c else some a :=
  @argmax_concat _ (OrderDual β) _ _ _ _

theorem argmax_cons (f : α → β) (a : α) (l : List α) :
  argmax f (a :: l) = Option.casesOn (argmax f l) (some a) fun c => if f c ≤ f a then some a else some c :=
  List.reverseRecOn l rfl$
    fun hd tl ih =>
      by 
        rw [←cons_append, argmax_concat, ih, argmax_concat]
        cases' h : argmax f hd with m
        ·
          simp [h]
        ·
          simp [h]
          dsimp 
          byCases' ham : f m ≤ f a
          ·
            rw [if_pos ham]
            dsimp 
            byCases' htlm : f tl ≤ f m
            ·
              rw [if_pos htlm]
              dsimp 
              rw [if_pos (le_transₓ htlm ham), if_pos ham]
            ·
              rw [if_neg htlm]
          ·
            rw [if_neg ham]
            dsimp 
            byCases' htlm : f tl ≤ f m
            ·
              rw [if_pos htlm]
              dsimp 
              rw [if_neg ham]
            ·
              rw [if_neg htlm]
              dsimp 
              rw [if_neg (not_le_of_gtₓ (lt_transₓ (lt_of_not_geₓ ham) (lt_of_not_geₓ htlm)))]

theorem argmin_cons (f : α → β) (a : α) (l : List α) :
  argmin f (a :: l) = Option.casesOn (argmin f l) (some a) fun c => if f a ≤ f c then some a else some c :=
  @argmax_cons _ (OrderDual β) _ _ _ _

-- error in Data.List.MinMax: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem index_of_argmax
[decidable_eq α]
{f : α → β} : ∀
{l : list α}
{m : α}, «expr ∈ »(m, argmax f l) → ∀ {a}, «expr ∈ »(a, l) → «expr ≤ »(f m, f a) → «expr ≤ »(l.index_of m, l.index_of a)
| «expr[ , ]»([]), m, _, _, _, _ := by simp [] [] [] [] [] []
| «expr :: »(hd, tl), m, hm, a, ha, ham := begin
  simp [] [] ["only"] ["[", expr index_of_cons, ",", expr argmax_cons, ",", expr option.mem_def, "]"] [] ["at", "⊢", ident hm],
  cases [expr h, ":", expr argmax f tl] [],
  { rw [expr h] ["at", ident hm],
    simp [] [] [] ["*"] [] ["at", "*"] },
  { rw [expr h] ["at", ident hm],
    dsimp ["only"] [] [] ["at", ident hm],
    cases [expr ha] ["with", ident hahd, ident hatl],
    { clear [ident index_of_argmax],
      subst [expr hahd],
      split_ifs ["at", ident hm] [],
      { subst [expr hm] },
      { subst [expr hm],
        contradiction } },
    { have [] [] [":=", expr index_of_argmax h hatl],
      clear [ident index_of_argmax],
      split_ifs ["at", "*"] []; refl <|> exact [expr nat.zero_le _] <|> simp [] [] [] ["[", "*", ",", expr nat.succ_le_succ_iff, ",", "-", ident not_le, "]"] [] ["at", "*"] } }
end

theorem index_of_argmin [DecidableEq α] {f : α → β} :
  ∀ {l : List α} {m : α}, m ∈ argmin f l → ∀ {a}, a ∈ l → f a ≤ f m → l.index_of m ≤ l.index_of a :=
  @index_of_argmax _ (OrderDual β) _ _ _

-- error in Data.List.MinMax: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_argmax_iff
[decidable_eq α]
{f : α → β}
{m : α}
{l : list α} : «expr ↔ »(«expr ∈ »(m, argmax f l), «expr ∧ »(«expr ∈ »(m, l), «expr ∧ »(∀
   a «expr ∈ » l, «expr ≤ »(f a, f m), ∀
   a «expr ∈ » l, «expr ≤ »(f m, f a) → «expr ≤ »(l.index_of m, l.index_of a)))) :=
⟨λ hm, ⟨argmax_mem hm, λ a ha, le_argmax_of_mem ha hm, λ _, index_of_argmax hm⟩, begin
   rintros ["⟨", ident hml, ",", ident ham, ",", ident hma, "⟩"],
   cases [expr harg, ":", expr argmax f l] ["with", ident n],
   { simp [] [] [] ["*"] [] ["at", "*"] },
   { have [] [] [":=", expr le_antisymm (hma n (argmax_mem harg) (le_argmax_of_mem hml harg)) (index_of_argmax harg hml (ham _ (argmax_mem harg)))],
     rw ["[", expr (index_of_inj hml (argmax_mem harg)).1 this, ",", expr option.mem_def, "]"] [] }
 end⟩

theorem argmax_eq_some_iff [DecidableEq α] {f : α → β} {m : α} {l : List α} :
  argmax f l = some m ↔ m ∈ l ∧ (∀ a _ : a ∈ l, f a ≤ f m) ∧ ∀ a _ : a ∈ l, f m ≤ f a → l.index_of m ≤ l.index_of a :=
  mem_argmax_iff

theorem mem_argmin_iff [DecidableEq α] {f : α → β} {m : α} {l : List α} :
  m ∈ argmin f l ↔ m ∈ l ∧ (∀ a _ : a ∈ l, f m ≤ f a) ∧ ∀ a _ : a ∈ l, f a ≤ f m → l.index_of m ≤ l.index_of a :=
  @mem_argmax_iff _ (OrderDual β) _ _ _ _ _

theorem argmin_eq_some_iff [DecidableEq α] {f : α → β} {m : α} {l : List α} :
  argmin f l = some m ↔ m ∈ l ∧ (∀ a _ : a ∈ l, f m ≤ f a) ∧ ∀ a _ : a ∈ l, f a ≤ f m → l.index_of m ≤ l.index_of a :=
  mem_argmin_iff

variable [LinearOrderₓ α]

/-- `maximum l` returns an `with_bot α`, the largest element of `l` for nonempty lists, and `⊥` for
`[]`  -/
def maximum (l : List α) : WithBot α :=
  argmax id l

/-- `minimum l` returns an `with_top α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`  -/
def minimum (l : List α) : WithTop α :=
  argmin id l

@[simp]
theorem maximum_nil : maximum ([] : List α) = ⊥ :=
  rfl

@[simp]
theorem minimum_nil : minimum ([] : List α) = ⊤ :=
  rfl

@[simp]
theorem maximum_singleton (a : α) : maximum [a] = a :=
  rfl

@[simp]
theorem minimum_singleton (a : α) : minimum [a] = a :=
  rfl

theorem maximum_mem {l : List α} {m : α} : (maximum l : WithTop α) = m → m ∈ l :=
  argmax_mem

theorem minimum_mem {l : List α} {m : α} : (minimum l : WithBot α) = m → m ∈ l :=
  argmin_mem

@[simp]
theorem maximum_eq_none {l : List α} : l.maximum = none ↔ l = [] :=
  argmax_eq_none

@[simp]
theorem minimum_eq_none {l : List α} : l.minimum = none ↔ l = [] :=
  argmin_eq_none

theorem le_maximum_of_mem {a m : α} {l : List α} : a ∈ l → (maximum l : WithBot α) = m → a ≤ m :=
  le_argmax_of_mem

theorem minimum_le_of_mem {a m : α} {l : List α} : a ∈ l → (minimum l : WithTop α) = m → m ≤ a :=
  argmin_le_of_mem

theorem le_maximum_of_mem' {a : α} {l : List α} (ha : a ∈ l) : (a : WithBot α) ≤ maximum l :=
  Option.casesOn (maximum l) (fun _ h => absurd ha ((h rfl).symm ▸ not_mem_nil _))
    (fun m hm _ => WithBot.coe_le_coe.2$ hm _ rfl) (fun m => @le_maximum_of_mem _ _ _ m _ ha) (@maximum_eq_none _ _ l).1

theorem le_minimum_of_mem' {a : α} {l : List α} (ha : a ∈ l) : minimum l ≤ (a : WithTop α) :=
  @le_maximum_of_mem' (OrderDual α) _ _ _ ha

theorem maximum_concat (a : α) (l : List α) : maximum (l ++ [a]) = max (maximum l) a :=
  by 
    rw [max_commₓ]
    simp only [maximum, argmax_concat, id]
    cases h : argmax id l
    ·
      rw [max_eq_leftₓ]
      rfl 
      exact bot_le 
    change (coeₓ : α → WithBot α) with some 
    rw [max_commₓ]
    simp [max_def]

theorem minimum_concat (a : α) (l : List α) : minimum (l ++ [a]) = min (minimum l) a :=
  @maximum_concat (OrderDual α) _ _ _

theorem maximum_cons (a : α) (l : List α) : maximum (a :: l) = max a (maximum l) :=
  List.reverseRecOn l
    (by 
      simp [@max_eq_leftₓ (WithBot α) _ _ _ bot_le])
    fun tl hd ih =>
      by 
        rw [←cons_append, maximum_concat, ih, maximum_concat, max_assocₓ]

theorem minimum_cons (a : α) (l : List α) : minimum (a :: l) = min a (minimum l) :=
  @maximum_cons (OrderDual α) _ _ _

-- error in Data.List.MinMax: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem maximum_eq_coe_iff
{m : α}
{l : list α} : «expr ↔ »(«expr = »(maximum l, m), «expr ∧ »(«expr ∈ »(m, l), ∀ a «expr ∈ » l, «expr ≤ »(a, m))) :=
begin
  unfold_coes [],
  simp [] [] ["only"] ["[", expr maximum, ",", expr argmax_eq_some_iff, ",", expr id, "]"] [] [],
  split,
  { simp [] [] ["only"] ["[", expr true_and, ",", expr forall_true_iff, "]"] [] [] { contextual := tt } },
  { simp [] [] ["only"] ["[", expr true_and, ",", expr forall_true_iff, "]"] [] [] { contextual := tt },
    intros [ident h, ident a, ident hal, ident hma],
    rw ["[", expr le_antisymm hma (h.2 a hal), "]"] [] }
end

theorem minimum_eq_coe_iff {m : α} {l : List α} : minimum l = m ↔ m ∈ l ∧ ∀ a _ : a ∈ l, m ≤ a :=
  @maximum_eq_coe_iff (OrderDual α) _ _ _

section Fold

variable {M : Type _} [CanonicallyLinearOrderedAddMonoid M]

/-! Note: since there is no typeclass typeclass dual
to `canonically_linear_ordered_add_monoid α` we cannot express these lemmas generally for
`minimum`; instead we are limited to doing so on `order_dual α`. -/


theorem maximum_eq_coe_foldr_max_of_ne_nil (l : List M) (h : l ≠ []) : l.maximum = (l.foldr max ⊥ : M) :=
  by 
    induction' l with hd tl IH
    ·
      contradiction
    ·
      rw [maximum_cons, foldr, WithBot.coe_max]
      byCases' h : tl = []
      ·
        simp [h, -WithTop.coe_zero]
      ·
        simp [IH h]

theorem minimum_eq_coe_foldr_min_of_ne_nil (l : List (OrderDual M)) (h : l ≠ []) :
  l.minimum = (l.foldr min ⊤ : OrderDual M) :=
  maximum_eq_coe_foldr_max_of_ne_nil l h

theorem maximum_nat_eq_coe_foldr_max_of_ne_nil (l : List ℕ) (h : l ≠ []) : l.maximum = (l.foldr max 0 : ℕ) :=
  maximum_eq_coe_foldr_max_of_ne_nil l h

-- error in Data.List.MinMax: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem max_le_of_forall_le
(l : list M)
(n : M)
(h : ∀ x «expr ∈ » l, «expr ≤ »(x, n)) : «expr ≤ »(l.foldr max «expr⊥»(), n) :=
begin
  induction [expr l] [] ["with", ident y, ident l, ident IH] [],
  { simp [] [] [] [] [] [] },
  { specialize [expr IH (λ x hx, h x (mem_cons_of_mem _ hx))],
    have [ident hy] [":", expr «expr ≤ »(y, n)] [":=", expr h y (mem_cons_self _ _)],
    simpa [] [] [] ["[", expr hy, "]"] [] ["using", expr IH] }
end

theorem le_min_of_le_forall (l : List (OrderDual M)) (n : OrderDual M) (h : ∀ x _ : x ∈ l, n ≤ x) : n ≤ l.foldr min ⊤ :=
  max_le_of_forall_le l n h

theorem max_nat_le_of_forall_le (l : List ℕ) (n : ℕ) (h : ∀ x _ : x ∈ l, x ≤ n) : l.foldr max 0 ≤ n :=
  max_le_of_forall_le l n h

end Fold

end List

