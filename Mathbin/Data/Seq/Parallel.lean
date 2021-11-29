import Mathbin.Data.Seq.Wseq

universe u v

namespace Computation

open Wseq

variable{α : Type u}{β : Type v}

def parallel.aux2 : List (Computation α) → Sum α (List (Computation α)) :=
  List.foldr
    (fun c o =>
      match o with 
      | Sum.inl a => Sum.inl a
      | Sum.inr ls => rmap (fun c' => c' :: ls) (destruct c))
    (Sum.inr [])

def parallel.aux1 : List (Computation α) × Wseq (Computation α) → Sum α (List (Computation α) × Wseq (Computation α))
| (l, S) =>
  rmap
    (fun l' =>
      match Seqₓₓ.destruct S with 
      | none => (l', nil)
      | some (none, S') => (l', S')
      | some (some c, S') => (c :: l', S'))
    (parallel.aux2 l)

/-- Parallel computation of an infinite stream of computations,
  taking the first result -/
def parallel (S : Wseq (Computation α)) : Computation α :=
  corec parallel.aux1 ([], S)

-- error in Data.Seq.Parallel: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem terminates_parallel.aux : ∀
{l : list (computation α)}
{S c}, «expr ∈ »(c, l) → terminates c → terminates (corec parallel.aux1 (l, S)) :=
begin
  have [ident lem1] [":", expr ∀
   l S, «expr∃ , »((a : α), «expr = »(parallel.aux2 l, sum.inl a)) → terminates (corec parallel.aux1 (l, S))] [],
  { intros [ident l, ident S, ident e],
    cases [expr e] ["with", ident a, ident e],
    have [ident this] [":", expr «expr = »(corec parallel.aux1 (l, S), return a)] [],
    { apply [expr destruct_eq_ret],
      simp [] [] [] ["[", expr parallel.aux1, "]"] [] [],
      rw [expr e] [],
      simp [] [] [] ["[", expr rmap, "]"] [] [] },
    rw [expr this] [],
    apply_instance },
  intros [ident l, ident S, ident c, ident m, ident T],
  revert [ident l, ident S],
  apply [expr @terminates_rec_on _ _ c T _ _],
  { intros [ident a, ident l, ident S, ident m],
    apply [expr lem1],
    induction [expr l] [] ["with", ident c, ident l, ident IH] ["generalizing", ident m]; simp [] [] [] [] [] ["at", ident m],
    { contradiction },
    cases [expr m] ["with", ident e, ident m],
    { rw ["<-", expr e] [],
      simp [] [] [] ["[", expr parallel.aux2, "]"] [] [],
      cases [expr list.foldr parallel.aux2._match_1 (sum.inr list.nil) l] ["with", ident a', ident ls],
      exacts ["[", expr ⟨a', rfl⟩, ",", expr ⟨a, rfl⟩, "]"] },
    { cases [expr IH m] ["with", ident a', ident e],
      simp [] [] [] ["[", expr parallel.aux2, "]"] [] [],
      simp [] [] [] ["[", expr parallel.aux2, "]"] [] ["at", ident e],
      rw [expr e] [],
      exact [expr ⟨a', rfl⟩] } },
  { intros [ident s, ident IH, ident l, ident S, ident m],
    have [ident H1] [":", expr ∀ l', «expr = »(parallel.aux2 l, sum.inr l') → «expr ∈ »(s, l')] [],
    { induction [expr l] [] ["with", ident c, ident l, ident IH'] ["generalizing", ident m]; intros [ident l', ident e']; simp [] [] [] [] [] ["at", ident m],
      { contradiction },
      cases [expr m] ["with", ident e, ident m]; simp [] [] [] ["[", expr parallel.aux2, "]"] [] ["at", ident e'],
      { rw ["<-", expr e] ["at", ident e'],
        cases [expr list.foldr parallel.aux2._match_1 (sum.inr list.nil) l] ["with", ident a', ident ls]; injection [expr e'] ["with", ident e'],
        rw ["<-", expr e'] [],
        simp [] [] [] [] [] [] },
      { induction [expr e, ":", expr list.foldr parallel.aux2._match_1 (sum.inr list.nil) l] [] ["with", ident a', ident ls] []; rw [expr e] ["at", ident e'],
        { contradiction },
        have [] [] [":=", expr IH' m _ e],
        simp [] [] [] ["[", expr parallel.aux2, "]"] [] ["at", ident e'],
        cases [expr destruct c] []; injection [expr e'] ["with", ident h'],
        rw ["<-", expr h'] [],
        simp [] [] [] ["[", expr this, "]"] [] [] } },
    induction [expr h, ":", expr parallel.aux2 l] [] ["with", ident a, ident l'] [],
    { exact [expr lem1 _ _ ⟨a, h⟩] },
    { have [ident H2] [":", expr «expr = »(corec parallel.aux1 (l, S), think _)] [],
      { apply [expr destruct_eq_think],
        simp [] [] [] ["[", expr parallel.aux1, "]"] [] [],
        rw [expr h] [],
        simp [] [] [] ["[", expr rmap, "]"] [] [] },
      rw [expr H2] [],
      apply [expr @computation.think_terminates _ _ _],
      have [] [] [":=", expr H1 _ h],
      rcases [expr seq.destruct S, "with", "_", "|", "⟨", "_", "|", ident c, ",", ident S', "⟩"]; simp [] [] [] ["[", expr parallel.aux1, "]"] [] []; apply [expr IH]; simp [] [] [] ["[", expr this, "]"] [] [] } }
end

-- error in Data.Seq.Parallel: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem terminates_parallel
{S : wseq (computation α)}
{c}
(h : «expr ∈ »(c, S))
[T : terminates c] : terminates (parallel S) :=
suffices ∀
(n)
(l : list (computation α))
(S
 c), «expr ∨ »(«expr ∈ »(c, l), «expr = »(some (some c), seq.nth S n)) → terminates c → terminates (corec parallel.aux1 (l, S)), from let ⟨n, h⟩ := h in
this n «expr[ , ]»([]) S c (or.inr h) T,
begin
  intro [ident n],
  induction [expr n] [] ["with", ident n, ident IH] []; intros [ident l, ident S, ident c, ident o, ident T],
  { cases [expr o] ["with", ident a, ident a],
    { exact [expr terminates_parallel.aux a T] },
    have [ident H] [":", expr «expr = »(seq.destruct S, some (some c, _))] [],
    { unfold [ident seq.destruct, ident functor.map] [],
      rw ["<-", expr a] [],
      simp [] [] [] [] [] [] },
    induction [expr h, ":", expr parallel.aux2 l] [] ["with", ident a, ident l'] []; have [ident C] [":", expr «expr = »(corec parallel.aux1 (l, S), _)] [],
    { apply [expr destruct_eq_ret],
      simp [] [] [] ["[", expr parallel.aux1, "]"] [] [],
      rw ["[", expr h, "]"] [],
      simp [] [] [] ["[", expr rmap, "]"] [] [] },
    { rw [expr C] [],
      resetI,
      apply_instance },
    { apply [expr destruct_eq_think],
      simp [] [] [] ["[", expr parallel.aux1, "]"] [] [],
      rw ["[", expr h, ",", expr H, "]"] [],
      simp [] [] [] ["[", expr rmap, "]"] [] [] },
    { rw [expr C] [],
      apply [expr @computation.think_terminates _ _ _],
      apply [expr terminates_parallel.aux _ T],
      simp [] [] [] [] [] [] } },
  { cases [expr o] ["with", ident a, ident a],
    { exact [expr terminates_parallel.aux a T] },
    induction [expr h, ":", expr parallel.aux2 l] [] ["with", ident a, ident l'] []; have [ident C] [":", expr «expr = »(corec parallel.aux1 (l, S), _)] [],
    { apply [expr destruct_eq_ret],
      simp [] [] [] ["[", expr parallel.aux1, "]"] [] [],
      rw ["[", expr h, "]"] [],
      simp [] [] [] ["[", expr rmap, "]"] [] [] },
    { rw [expr C] [],
      resetI,
      apply_instance },
    { apply [expr destruct_eq_think],
      simp [] [] [] ["[", expr parallel.aux1, "]"] [] [],
      rw ["[", expr h, "]"] [],
      simp [] [] [] ["[", expr rmap, "]"] [] [] },
    { rw [expr C] [],
      apply [expr @computation.think_terminates _ _ _],
      have [ident TT] [":", expr ∀ l', terminates (corec parallel.aux1 (l', S.tail))] [],
      { intro [],
        apply [expr IH _ _ _ (or.inr _) T],
        rw [expr a] [],
        cases [expr S] ["with", ident f, ident al],
        refl },
      induction [expr e, ":", expr seq.nth S 0] [] ["with", ident o] [],
      { have [ident D] [":", expr «expr = »(seq.destruct S, none)] [],
        { dsimp [] ["[", expr seq.destruct, "]"] [] [],
          rw [expr e] [],
          refl },
        rw [expr D] [],
        simp [] [] [] ["[", expr parallel.aux1, "]"] [] [],
        have [ident TT] [] [":=", expr TT l'],
        rwa ["[", expr seq.destruct_eq_nil D, ",", expr seq.tail_nil, "]"] ["at", ident TT] },
      { have [ident D] [":", expr «expr = »(seq.destruct S, some (o, S.tail))] [],
        { dsimp [] ["[", expr seq.destruct, "]"] [] [],
          rw [expr e] [],
          refl },
        rw [expr D] [],
        cases [expr o] ["with", ident c]; simp [] [] [] ["[", expr parallel.aux1, ",", expr TT, "]"] [] [] } } }
end

-- error in Data.Seq.Parallel: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_of_mem_parallel
{S : wseq (computation α)}
{a}
(h : «expr ∈ »(a, parallel S)) : «expr∃ , »((c «expr ∈ » S), «expr ∈ »(a, c)) :=
suffices ∀
C, «expr ∈ »(a, C) → ∀
(l : list (computation α))
(S), «expr = »(corec parallel.aux1 (l, S), C) → «expr∃ , »((c), «expr ∧ »(«expr ∨ »(«expr ∈ »(c, l), «expr ∈ »(c, S)), «expr ∈ »(a, c))), from let ⟨c, h1, h2⟩ := this _ h «expr[ , ]»([]) S rfl in
⟨c, h1.resolve_left id, h2⟩,
begin
  let [ident F] [":", expr list (computation α) → «expr ⊕ »(α, list (computation α)) → exprProp()] [],
  { intros [ident l, ident a],
    cases [expr a] ["with", ident a, ident l'],
    exact [expr «expr∃ , »((c «expr ∈ » l), «expr ∈ »(a, c))],
    exact [expr ∀ a', «expr∃ , »((c «expr ∈ » l'), «expr ∈ »(a', c)) → «expr∃ , »((c «expr ∈ » l), «expr ∈ »(a', c))] },
  have [ident lem1] [":", expr ∀ l : list (computation α), F l (parallel.aux2 l)] [],
  { intro [ident l],
    induction [expr l] [] ["with", ident c, ident l, ident IH] []; simp [] [] [] ["[", expr parallel.aux2, "]"] [] [],
    { intros [ident a, ident h],
      rcases [expr h, "with", "⟨", ident c, ",", ident hn, ",", "_", "⟩"],
      exact [expr false.elim hn] },
    { simp [] [] [] ["[", expr parallel.aux2, "]"] [] ["at", ident IH],
      cases [expr list.foldr parallel.aux2._match_1 (sum.inr list.nil) l] ["with", ident a, ident ls]; simp [] [] [] ["[", expr parallel.aux2, "]"] [] [],
      { rcases [expr IH, "with", "⟨", ident c', ",", ident cl, ",", ident ac, "⟩"],
        refine [expr ⟨c', or.inr cl, ac⟩] },
      { induction [expr h, ":", expr destruct c] [] ["with", ident a, ident c'] []; simp [] [] [] ["[", expr rmap, "]"] [] [],
        { refine [expr ⟨c, list.mem_cons_self _ _, _⟩],
          rw [expr destruct_eq_ret h] [],
          apply [expr ret_mem] },
        { intros [ident a', ident h],
          rcases [expr h, "with", "⟨", ident d, ",", ident dm, ",", ident ad, "⟩"],
          simp [] [] [] [] [] ["at", ident dm],
          cases [expr dm] ["with", ident e, ident dl],
          { rw [expr e] ["at", ident ad],
            refine [expr ⟨c, list.mem_cons_self _ _, _⟩],
            rw [expr destruct_eq_think h] [],
            exact [expr think_mem ad] },
          { cases [expr IH a' ⟨d, dl, ad⟩] ["with", ident d, ident dm],
            cases [expr dm] ["with", ident dm, ident ad],
            exact [expr ⟨d, or.inr dm, ad⟩] } } } } },
  intros [ident C, ident aC],
  refine [expr mem_rec_on aC _ (λ
    C'
    IH, _)]; intros [ident l, ident S, ident e]; have [ident e'] [] [":=", expr congr_arg destruct e]; have [] [] [":=", expr lem1 l]; simp [] [] [] ["[", expr parallel.aux1, "]"] [] ["at", ident e']; cases [expr parallel.aux2 l] ["with", ident a', ident l']; injection [expr e'] ["with", ident h'],
  { rw [expr h'] ["at", ident this],
    rcases [expr this, "with", "⟨", ident c, ",", ident cl, ",", ident ac, "⟩"],
    exact [expr ⟨c, or.inl cl, ac⟩] },
  { induction [expr e, ":", expr seq.destruct S] [] ["with", ident a] []; rw [expr e] ["at", ident h'],
    { exact [expr let ⟨d, o, ad⟩ := IH _ _ h', ⟨c, cl, ac⟩ := this a ⟨d, o.resolve_right (not_mem_nil _), ad⟩ in
       ⟨c, or.inl cl, ac⟩] },
    { cases [expr a] ["with", ident o, ident S'],
      cases [expr o] ["with", ident c]; simp [] [] [] ["[", expr parallel.aux1, "]"] [] ["at", ident h']; rcases [expr IH _ _ h', "with", "⟨", ident d, ",", ident dl, "|", ident dS', ",", ident ad, "⟩"],
      { exact [expr let ⟨c, cl, ac⟩ := this a ⟨d, dl, ad⟩ in ⟨c, or.inl cl, ac⟩] },
      { refine [expr ⟨d, or.inr _, ad⟩],
        rw [expr seq.destruct_eq_cons e] [],
        exact [expr seq.mem_cons_of_mem _ dS'] },
      { simp [] [] [] [] [] ["at", ident dl],
        cases [expr dl] ["with", ident dc, ident dl],
        { rw [expr dc] ["at", ident ad],
          refine [expr ⟨c, or.inr _, ad⟩],
          rw [expr seq.destruct_eq_cons e] [],
          apply [expr seq.mem_cons] },
        { exact [expr let ⟨c, cl, ac⟩ := this a ⟨d, dl, ad⟩ in ⟨c, or.inl cl, ac⟩] } },
      { refine [expr ⟨d, or.inr _, ad⟩],
        rw [expr seq.destruct_eq_cons e] [],
        exact [expr seq.mem_cons_of_mem _ dS'] } } }
end

-- error in Data.Seq.Parallel: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_parallel (f : α → β) (S) : «expr = »(map f (parallel S), parallel (S.map (map f))) :=
begin
  refine [expr eq_of_bisim (λ
    c1
    c2, «expr∃ , »((l
      S), «expr ∧ »(«expr = »(c1, map f (corec parallel.aux1 (l, S))), «expr = »(c2, corec parallel.aux1 (l.map (map f), S.map (map f)))))) _ ⟨«expr[ , ]»([]), S, rfl, rfl⟩],
  intros [ident c1, ident c2, ident h],
  exact [expr match c1, c2, h with
   | ._, ._, ⟨l, S, rfl, rfl⟩ := begin
     clear [ident _match],
     have [] [":", expr «expr = »(parallel.aux2 (l.map (map f)), lmap f (rmap (list.map (map f)) (parallel.aux2 l)))] [],
     { simp [] [] [] ["[", expr parallel.aux2, "]"] [] [],
       induction [expr l] [] ["with", ident c, ident l, ident IH] []; simp [] [] [] [] [] [],
       rw ["[", expr IH, "]"] [],
       cases [expr list.foldr parallel.aux2._match_1 (sum.inr list.nil) l] []; simp [] [] [] ["[", expr parallel.aux2, "]"] [] [],
       cases [expr destruct c] []; simp [] [] [] [] [] [] },
     simp [] [] [] ["[", expr parallel.aux1, "]"] [] [],
     rw [expr this] [],
     cases [expr parallel.aux2 l] ["with", ident a, ident l']; simp [] [] [] [] [] [],
     apply [expr S.cases_on _ (λ
       c
       S, _) (λ
       S, _)]; simp [] [] [] [] [] []; simp [] [] [] ["[", expr parallel.aux1, "]"] [] []; exact [expr ⟨_, _, rfl, rfl⟩]
   end
   end]
end

theorem parallel_empty (S : Wseq (Computation α)) (h : S.head ~> none) : parallel S = Empty _ :=
  eq_empty_of_not_terminates$
    fun ⟨⟨a, m⟩⟩ =>
      let ⟨c, cs, ac⟩ := exists_of_mem_parallel m 
      let ⟨n, nm⟩ := exists_nth_of_mem cs 
      let ⟨c', h'⟩ := head_some_of_nth_some nm 
      by 
        injection h h'

-- error in Data.Seq.Parallel: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
def parallel_rec
{S : wseq (computation α)}
(C : α → Sort v)
(H : ∀ s «expr ∈ » S, ∀ a «expr ∈ » s, C a)
{a}
(h : «expr ∈ »(a, parallel S)) : C a :=
begin
  let [ident T] [":", expr wseq (computation «expr × »(α, computation α))] [":=", expr S.map (λ
    c, c.map (λ a, (a, c)))],
  have [] [":", expr «expr = »(S, T.map (map (λ c, c.1)))] [],
  { rw ["[", "<-", expr wseq.map_comp, "]"] [],
    refine [expr (wseq.map_id _).symm.trans (congr_arg (λ f, wseq.map f S) _)],
    funext [ident c],
    dsimp [] ["[", expr id, ",", expr function.comp, "]"] [] [],
    rw ["[", "<-", expr map_comp, "]"] [],
    exact [expr (map_id _).symm] },
  have [ident pe] [] [":=", expr congr_arg parallel this],
  rw ["<-", expr map_parallel] ["at", ident pe],
  have [ident h'] [] [":=", expr h],
  rw [expr pe] ["at", ident h'],
  haveI [] [":", expr terminates (parallel T)] [":=", expr (terminates_map_iff _ _).1 ⟨⟨_, h'⟩⟩],
  induction [expr e, ":", expr get (parallel T)] [] ["with", ident a', ident c] [],
  have [] [":", expr «expr ∧ »(«expr ∈ »(a, c), «expr ∈ »(c, S))] [],
  { rcases [expr exists_of_mem_map h', "with", "⟨", ident d, ",", ident dT, ",", ident cd, "⟩"],
    rw [expr get_eq_of_mem _ dT] ["at", ident e],
    cases [expr e] [],
    dsimp [] [] [] ["at", ident cd],
    cases [expr cd] [],
    rcases [expr exists_of_mem_parallel dT, "with", "⟨", ident d', ",", ident dT', ",", ident ad', "⟩"],
    rcases [expr wseq.exists_of_mem_map dT', "with", "⟨", ident c', ",", ident cs', ",", ident e', "⟩"],
    rw ["<-", expr e'] ["at", ident ad'],
    rcases [expr exists_of_mem_map ad', "with", "⟨", ident a', ",", ident ac', ",", ident e', "⟩"],
    injection [expr e'] ["with", ident i1, ident i2],
    constructor,
    rwa ["[", expr i1, ",", expr i2, "]"] ["at", ident ac'],
    rwa [expr i2] ["at", ident cs'] },
  cases [expr this] ["with", ident ac, ident cs],
  apply [expr H _ cs _ ac]
end

theorem parallel_promises {S : Wseq (Computation α)} {a} (H : ∀ s (_ : s ∈ S), s ~> a) : parallel S ~> a :=
  fun a' ma' =>
    let ⟨c, cs, ac⟩ := exists_of_mem_parallel ma' 
    H _ cs ac

-- error in Data.Seq.Parallel: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_parallel
{S : wseq (computation α)}
{a}
(H : ∀ s «expr ∈ » S, «expr ~> »(s, a))
{c}
(cs : «expr ∈ »(c, S))
(ac : «expr ∈ »(a, c)) : «expr ∈ »(a, parallel S) :=
by haveI [] [] [":=", expr terminates_of_mem ac]; haveI [] [] [":=", expr terminates_parallel cs]; exact [expr mem_of_promises _ (parallel_promises H)]

theorem parallel_congr_lem {S T : Wseq (Computation α)} {a} (H : S.lift_rel Equiv T) :
  (∀ s (_ : s ∈ S), s ~> a) ↔ ∀ t (_ : t ∈ T), t ~> a :=
  ⟨fun h1 t tT =>
      let ⟨s, sS, se⟩ := Wseq.exists_of_lift_rel_right H tT
      (promises_congr se _).1 (h1 _ sS),
    fun h2 s sS =>
      let ⟨t, tT, se⟩ := Wseq.exists_of_lift_rel_left H sS
      (promises_congr se _).2 (h2 _ tT)⟩

-- error in Data.Seq.Parallel: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem parallel_congr_left
{S T : wseq (computation α)}
{a}
(h1 : ∀ s «expr ∈ » S, «expr ~> »(s, a))
(H : S.lift_rel equiv T) : [«expr ~ »/«expr ~ »](parallel S, parallel T) :=
let h2 := (parallel_congr_lem H).1 h1 in
λ
a', ⟨λ
 h, by have [ident aa] [] [":=", expr parallel_promises h1 h]; rw ["<-", expr aa] []; rw ["<-", expr aa] ["at", ident h]; exact [expr let ⟨s, sS, as⟩ := exists_of_mem_parallel h,
      ⟨t, tT, st⟩ := wseq.exists_of_lift_rel_left H sS,
      aT := (st _).1 as in
  mem_parallel h2 tT aT], λ
 h, by have [ident aa] [] [":=", expr parallel_promises h2 h]; rw ["<-", expr aa] []; rw ["<-", expr aa] ["at", ident h]; exact [expr let ⟨s, sS, as⟩ := exists_of_mem_parallel h,
      ⟨t, tT, st⟩ := wseq.exists_of_lift_rel_right H sS,
      aT := (st _).2 as in
  mem_parallel h1 tT aT]⟩

theorem parallel_congr_right {S T : Wseq (Computation α)} {a} (h2 : ∀ t (_ : t ∈ T), t ~> a) (H : S.lift_rel Equiv T) :
  parallel S ~ parallel T :=
  parallel_congr_left ((parallel_congr_lem H).2 h2) H

end Computation

