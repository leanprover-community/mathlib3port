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

-- error in Data.Seq.Parallel: ././Mathport/Syntax/Translate/Basic.lean:340:40: in exacts: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
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

theorem terminates_parallel {S : Wseq (Computation α)} {c} (h : c ∈ S) [T : terminates c] : terminates (parallel S) :=
  suffices
    ∀ n l : List (Computation α) S c,
      c ∈ l ∨ some (some c) = Seqₓₓ.nth S n → terminates c → terminates (corec parallel.aux1 (l, S)) from
    let ⟨n, h⟩ := h 
    this n [] S c (Or.inr h) T 
  by 
    intro n 
    induction' n with n IH <;> intro l S c o T
    ·
      cases' o with a a
      ·
        exact terminates_parallel.aux a T 
      have H : Seqₓₓ.destruct S = some (some c, _)
      ·
        unfold Seqₓₓ.destruct Functor.map 
        rw [←a]
        simp 
      induction' h : parallel.aux2 l with a l' <;> have C : corec parallel.aux1 (l, S) = _
      ·
        apply destruct_eq_ret 
        simp [parallel.aux1]
        rw [h]
        simp [rmap]
      ·
        rw [C]
        resetI 
        infer_instance
      ·
        apply destruct_eq_think 
        simp [parallel.aux1]
        rw [h, H]
        simp [rmap]
      ·
        rw [C]
        apply @Computation.think_terminates _ _ _ 
        apply terminates_parallel.aux _ T 
        simp 
    ·
      cases' o with a a
      ·
        exact terminates_parallel.aux a T 
      induction' h : parallel.aux2 l with a l' <;> have C : corec parallel.aux1 (l, S) = _
      ·
        apply destruct_eq_ret 
        simp [parallel.aux1]
        rw [h]
        simp [rmap]
      ·
        rw [C]
        resetI 
        infer_instance
      ·
        apply destruct_eq_think 
        simp [parallel.aux1]
        rw [h]
        simp [rmap]
      ·
        rw [C]
        apply @Computation.think_terminates _ _ _ 
        have TT : ∀ l', terminates (corec parallel.aux1 (l', S.tail))
        ·
          intro 
          apply IH _ _ _ (Or.inr _) T 
          rw [a]
          cases' S with f al 
          rfl 
        induction' e : Seqₓₓ.nth S 0 with o
        ·
          have D : Seqₓₓ.destruct S = none
          ·
            dsimp [Seqₓₓ.destruct]
            rw [e]
            rfl 
          rw [D]
          simp [parallel.aux1]
          have TT := TT l' 
          rwa [Seqₓₓ.destruct_eq_nil D, Seqₓₓ.tail_nil] at TT
        ·
          have D : Seqₓₓ.destruct S = some (o, S.tail)
          ·
            dsimp [Seqₓₓ.destruct]
            rw [e]
            rfl 
          rw [D]
          cases' o with c <;> simp [parallel.aux1, TT]

theorem exists_of_mem_parallel {S : Wseq (Computation α)} {a} (h : a ∈ parallel S) : ∃ (c : _)(_ : c ∈ S), a ∈ c :=
  suffices ∀ C, a ∈ C → ∀ l : List (Computation α) S, corec parallel.aux1 (l, S) = C → ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c from
    let ⟨c, h1, h2⟩ := this _ h [] S rfl
    ⟨c, h1.resolve_left id, h2⟩
  by 
    let F : List (Computation α) → Sum α (List (Computation α)) → Prop
    ·
      intro l a 
      cases' a with a l' 
      exact ∃ (c : _)(_ : c ∈ l), a ∈ c 
      exact ∀ a', (∃ (c : _)(_ : c ∈ l'), a' ∈ c) → ∃ (c : _)(_ : c ∈ l), a' ∈ c 
    have lem1 : ∀ l : List (Computation α), F l (parallel.aux2 l)
    ·
      intro l 
      induction' l with c l IH <;> simp [parallel.aux2]
      ·
        intro a h 
        rcases h with ⟨c, hn, _⟩
        exact False.elim hn
      ·
        simp [parallel.aux2] at IH 
        cases' List.foldr parallel.aux2._match_1 (Sum.inr List.nil) l with a ls <;> simp [parallel.aux2]
        ·
          rcases IH with ⟨c', cl, ac⟩
          refine' ⟨c', Or.inr cl, ac⟩
        ·
          induction' h : destruct c with a c' <;> simp [rmap]
          ·
            refine' ⟨c, List.mem_cons_selfₓ _ _, _⟩
            rw [destruct_eq_ret h]
            apply ret_mem
          ·
            intro a' h 
            rcases h with ⟨d, dm, ad⟩
            simp  at dm 
            cases' dm with e dl
            ·
              rw [e] at ad 
              refine' ⟨c, List.mem_cons_selfₓ _ _, _⟩
              rw [destruct_eq_think h]
              exact think_mem ad
            ·
              cases' IH a' ⟨d, dl, ad⟩ with d dm 
              cases' dm with dm ad 
              exact ⟨d, Or.inr dm, ad⟩
    intro C aC 
    refine' mem_rec_on aC _ fun C' IH => _ <;>
      intro l S e <;>
        have e' := congr_argₓ destruct e <;>
          have  := lem1 l <;> simp [parallel.aux1] at e' <;> cases' parallel.aux2 l with a' l' <;> injection e' with h'
    ·
      rw [h'] at this 
      rcases this with ⟨c, cl, ac⟩
      exact ⟨c, Or.inl cl, ac⟩
    ·
      induction' e : Seqₓₓ.destruct S with a <;> rw [e] at h'
      ·
        exact
          let ⟨d, o, ad⟩ := IH _ _ h' 
          let ⟨c, cl, ac⟩ := this a ⟨d, o.resolve_right (not_mem_nil _), ad⟩
          ⟨c, Or.inl cl, ac⟩
      ·
        cases' a with o S' 
        cases' o with c <;> simp [parallel.aux1] at h' <;> rcases IH _ _ h' with ⟨d, dl | dS', ad⟩
        ·
          exact
            let ⟨c, cl, ac⟩ := this a ⟨d, dl, ad⟩
            ⟨c, Or.inl cl, ac⟩
        ·
          refine' ⟨d, Or.inr _, ad⟩
          rw [Seqₓₓ.destruct_eq_cons e]
          exact Seqₓₓ.mem_cons_of_mem _ dS'
        ·
          simp  at dl 
          cases' dl with dc dl
          ·
            rw [dc] at ad 
            refine' ⟨c, Or.inr _, ad⟩
            rw [Seqₓₓ.destruct_eq_cons e]
            apply Seqₓₓ.mem_cons
          ·
            exact
              let ⟨c, cl, ac⟩ := this a ⟨d, dl, ad⟩
              ⟨c, Or.inl cl, ac⟩
        ·
          refine' ⟨d, Or.inr _, ad⟩
          rw [Seqₓₓ.destruct_eq_cons e]
          exact Seqₓₓ.mem_cons_of_mem _ dS'

theorem map_parallel (f : α → β) S : map f (parallel S) = parallel (S.map (map f)) :=
  by 
    refine'
      eq_of_bisim
        (fun c1 c2 =>
          ∃ l S, c1 = map f (corec parallel.aux1 (l, S)) ∧ c2 = corec parallel.aux1 (l.map (map f), S.map (map f)))
        _ ⟨[], S, rfl, rfl⟩
    intro c1 c2 h 
    exact
      match c1, c2, h with 
      | _, _, ⟨l, S, rfl, rfl⟩ =>
        by 
          clear _match 
          have  : parallel.aux2 (l.map (map f)) = lmap f (rmap (List.map (map f)) (parallel.aux2 l))
          ·
            simp [parallel.aux2]
            induction' l with c l IH <;> simp 
            rw [IH]
            cases List.foldr parallel.aux2._match_1 (Sum.inr List.nil) l <;> simp [parallel.aux2]
            cases destruct c <;> simp 
          simp [parallel.aux1]
          rw [this]
          cases' parallel.aux2 l with a l' <;> simp 
          apply S.cases_on _ (fun c S => _) fun S => _ <;> simp  <;> simp [parallel.aux1] <;> exact ⟨_, _, rfl, rfl⟩

theorem parallel_empty (S : Wseq (Computation α)) (h : S.head ~> none) : parallel S = Empty _ :=
  eq_empty_of_not_terminates$
    fun ⟨⟨a, m⟩⟩ =>
      let ⟨c, cs, ac⟩ := exists_of_mem_parallel m 
      let ⟨n, nm⟩ := exists_nth_of_mem cs 
      let ⟨c', h'⟩ := head_some_of_nth_some nm 
      by 
        injection h h'

def parallel_rec {S : Wseq (Computation α)} (C : α → Sort v) (H : ∀ s _ : s ∈ S, ∀ a _ : a ∈ s, C a) {a}
  (h : a ∈ parallel S) : C a :=
  by 
    let T : Wseq (Computation (α × Computation α)) := S.map fun c => c.map fun a => (a, c)
    have  : S = T.map (map fun c => c.1)
    ·
      rw [←Wseq.map_comp]
      refine' (Wseq.map_id _).symm.trans (congr_argₓ (fun f => Wseq.map f S) _)
      funext c 
      dsimp [id, Function.comp]
      rw [←map_comp]
      exact (map_id _).symm 
    have pe := congr_argₓ parallel this 
    rw [←map_parallel] at pe 
    have h' := h 
    rw [pe] at h' 
    haveI  : terminates (parallel T) := (terminates_map_iff _ _).1 ⟨⟨_, h'⟩⟩
    induction' e : get (parallel T) with a' c 
    have  : a ∈ c ∧ c ∈ S
    ·
      rcases exists_of_mem_map h' with ⟨d, dT, cd⟩
      rw [get_eq_of_mem _ dT] at e 
      cases e 
      dsimp  at cd 
      cases cd 
      rcases exists_of_mem_parallel dT with ⟨d', dT', ad'⟩
      rcases Wseq.exists_of_mem_map dT' with ⟨c', cs', e'⟩
      rw [←e'] at ad' 
      rcases exists_of_mem_map ad' with ⟨a', ac', e'⟩
      injection e' with i1 i2 
      constructor 
      rwa [i1, i2] at ac' 
      rwa [i2] at cs' 
    cases' this with ac cs 
    apply H _ cs _ ac

theorem parallel_promises {S : Wseq (Computation α)} {a} (H : ∀ s _ : s ∈ S, s ~> a) : parallel S ~> a :=
  fun a' ma' =>
    let ⟨c, cs, ac⟩ := exists_of_mem_parallel ma' 
    H _ cs ac

theorem mem_parallel {S : Wseq (Computation α)} {a} (H : ∀ s _ : s ∈ S, s ~> a) {c} (cs : c ∈ S) (ac : a ∈ c) :
  a ∈ parallel S :=
  by 
    haveI  := terminates_of_mem ac <;>
      haveI  := terminates_parallel cs <;> exact mem_of_promises _ (parallel_promises H)

theorem parallel_congr_lem {S T : Wseq (Computation α)} {a} (H : S.lift_rel Equiv T) :
  (∀ s _ : s ∈ S, s ~> a) ↔ ∀ t _ : t ∈ T, t ~> a :=
  ⟨fun h1 t tT =>
      let ⟨s, sS, se⟩ := Wseq.exists_of_lift_rel_right H tT
      (promises_congr se _).1 (h1 _ sS),
    fun h2 s sS =>
      let ⟨t, tT, se⟩ := Wseq.exists_of_lift_rel_left H sS
      (promises_congr se _).2 (h2 _ tT)⟩

theorem parallel_congr_left {S T : Wseq (Computation α)} {a} (h1 : ∀ s _ : s ∈ S, s ~> a) (H : S.lift_rel Equiv T) :
  parallel S ~ parallel T :=
  let h2 := (parallel_congr_lem H).1 h1 
  fun a' =>
    ⟨fun h =>
        by 
          have aa := parallel_promises h1 h <;>
            rw [←aa] <;>
              rw [←aa] at h <;>
                exact
                  let ⟨s, sS, as⟩ := exists_of_mem_parallel h 
                  let ⟨t, tT, st⟩ := Wseq.exists_of_lift_rel_left H sS 
                  let aT := (st _).1 as 
                  mem_parallel h2 tT aT,
      fun h =>
        by 
          have aa := parallel_promises h2 h <;>
            rw [←aa] <;>
              rw [←aa] at h <;>
                exact
                  let ⟨s, sS, as⟩ := exists_of_mem_parallel h 
                  let ⟨t, tT, st⟩ := Wseq.exists_of_lift_rel_right H sS 
                  let aT := (st _).2 as 
                  mem_parallel h1 tT aT⟩

theorem parallel_congr_right {S T : Wseq (Computation α)} {a} (h2 : ∀ t _ : t ∈ T, t ~> a) (H : S.lift_rel Equiv T) :
  parallel S ~ parallel T :=
  parallel_congr_left ((parallel_congr_lem H).2 h2) H

end Computation

