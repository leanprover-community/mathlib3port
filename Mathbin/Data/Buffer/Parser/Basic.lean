import Mathbin.Data.String.Basic 
import Mathbin.Data.Buffer.Basic 
import Mathbin.Data.Nat.Digits

/-!
# Parsers

`parser α` is the type that describes a computation that can ingest a `char_buffer`
and output, if successful, a term of type `α`.
This file expands on the definitions in the core library, proving that all the core library
parsers are `mono`. There are also lemmas on the composability of parsers.

## Main definitions

* `parse_result.pos` : The position of a `char_buffer` at which a `parser α` has finished.
* `parser.mono` : The property that a parser only moves forward within a buffer,
  in both cases of success or failure.

## Implementation details

Lemmas about how parsers are mono are in the `mono` namespace. That allows using projection
notation for shorter term proofs that are parallel to the definitions of the parsers in structure.

-/


open Parser ParseResult

/--
For some `parse_result α`, give the position at which the result was provided, in either the
`done` or the `fail` case.
-/
@[simp]
def ParseResult.pos {α} : ParseResult α → ℕ
| done n _ => n
| fail n _ => n

namespace Parser

section DefnLemmas

variable{α β : Type}(msgs : Thunkₓ (List Stringₓ))(msg : Thunkₓ Stringₓ)

variable(p q : Parser α)(cb : CharBuffer)(n n' : ℕ){err : Dlist Stringₓ}

variable{a : α}{b : β}

/--
A `p : parser α` is defined to be `mono` if the result `p cb n` it gives,
for some `cb : char_buffer` and `n : ℕ`, (whether `done` or `fail`),
is always at a `parse_result.pos` that is at least `n`.
The `mono` property is used mainly for proper `orelse` behavior.
-/
class mono : Prop where 
  le' : ∀ (cb : CharBuffer) (n : ℕ), n ≤ (p cb n).Pos

theorem mono.le [p.mono] : n ≤ (p cb n).Pos :=
  mono.le' cb n

/--
A `parser α` is defined to be `static` if it does not move on success.
-/
class static : Prop where 
  of_done : ∀ {cb : CharBuffer} {n n' : ℕ} {a : α}, p cb n = done n' a → n = n'

/--
A `parser α` is defined to be `err_static` if it does not move on error.
-/
class err_static : Prop where 
  of_fail : ∀ {cb : CharBuffer} {n n' : ℕ} {err : Dlist Stringₓ}, p cb n = fail n' err → n = n'

/--
A `parser α` is defined to be `step` if it always moves exactly one char forward on success.
-/
class step : Prop where 
  of_done : ∀ {cb : CharBuffer} {n n' : ℕ} {a : α}, p cb n = done n' a → n' = n+1

/--
A `parser α` is defined to be `prog` if it always moves forward on success.
-/
class prog : Prop where 
  of_done : ∀ {cb : CharBuffer} {n n' : ℕ} {a : α}, p cb n = done n' a → n < n'

/--
A `parser a` is defined to be `bounded` if it produces a
`fail` `parse_result` when it is parsing outside the provided `char_buffer`.
-/
class Bounded : Prop where 
  ex' : ∀ {cb : CharBuffer} {n : ℕ}, cb.size ≤ n → ∃ (n' : ℕ)(err : Dlist Stringₓ), p cb n = fail n' err

theorem bounded.exists (p : Parser α) [p.bounded] {cb : CharBuffer} {n : ℕ} (h : cb.size ≤ n) :
  ∃ (n' : ℕ)(err : Dlist Stringₓ), p cb n = fail n' err :=
  bounded.ex' h

/--
A `parser a` is defined to be `unfailing` if it always produces a `done` `parse_result`.
-/
class unfailing : Prop where 
  ex' : ∀ (cb : CharBuffer) (n : ℕ), ∃ (n' : ℕ)(a : α), p cb n = done n' a

/--
A `parser a` is defined to be `conditionally_unfailing` if it produces a
`done` `parse_result` as long as it is parsing within the provided `char_buffer`.
-/
class conditionally_unfailing : Prop where 
  ex' : ∀ {cb : CharBuffer} {n : ℕ}, n < cb.size → ∃ (n' : ℕ)(a : α), p cb n = done n' a

theorem fail_iff :
  (∀ pos' result, p cb n ≠ done pos' result) ↔ ∃ (pos' : ℕ)(err : Dlist Stringₓ), p cb n = fail pos' err :=
  by 
    cases p cb n <;> simp 

theorem success_iff : (∀ pos' err, p cb n ≠ fail pos' err) ↔ ∃ (pos' : ℕ)(result : α), p cb n = done pos' result :=
  by 
    cases p cb n <;> simp 

variable{p q cb n n' msgs msg}

theorem mono.of_done [p.mono] (h : p cb n = done n' a) : n ≤ n' :=
  by 
    simpa [h] using mono.le p cb n

theorem mono.of_fail [p.mono] (h : p cb n = fail n' err) : n ≤ n' :=
  by 
    simpa [h] using mono.le p cb n

theorem bounded.of_done [p.bounded] (h : p cb n = done n' a) : n < cb.size :=
  by 
    contrapose! h 
    obtain ⟨np, err, hp⟩ := bounded.exists p h 
    simp [hp]

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem static.iff : «expr ↔ »(static p, ∀
 (cb : char_buffer)
 (n n' : exprℕ())
 (a : α), «expr = »(p cb n, done n' a) → «expr = »(n, n')) :=
⟨λ h _ _ _ _ hp, by { haveI [] [] [":=", expr h], exact [expr static.of_done hp] }, λ h, ⟨h⟩⟩

theorem exists_done (p : Parser α) [p.unfailing] (cb : CharBuffer) (n : ℕ) : ∃ (n' : ℕ)(a : α), p cb n = done n' a :=
  unfailing.ex' cb n

theorem unfailing.of_fail [p.unfailing] (h : p cb n = fail n' err) : False :=
  by 
    obtain ⟨np, a, hp⟩ := p.exists_done cb n 
    simpa [hp] using h

instance (priority := 100)conditionally_unfailing_of_unfailing [p.unfailing] : conditionally_unfailing p :=
  ⟨fun _ _ _ => p.exists_done _ _⟩

theorem exists_done_in_bounds (p : Parser α) [p.conditionally_unfailing] {cb : CharBuffer} {n : ℕ} (h : n < cb.size) :
  ∃ (n' : ℕ)(a : α), p cb n = done n' a :=
  conditionally_unfailing.ex' h

theorem conditionally_unfailing.of_fail [p.conditionally_unfailing] (h : p cb n = fail n' err) (hn : n < cb.size) :
  False :=
  by 
    obtain ⟨np, a, hp⟩ := p.exists_done_in_bounds hn 
    simpa [hp] using h

theorem decorate_errors_fail (h : p cb n = fail n' err) :
  @decorate_errors α msgs p cb n = fail n (Dlist.lazyOfList (msgs ())) :=
  by 
    simp [decorate_errors, h]

theorem decorate_errors_success (h : p cb n = done n' a) : @decorate_errors α msgs p cb n = done n' a :=
  by 
    simp [decorate_errors, h]

theorem decorate_error_fail (h : p cb n = fail n' err) :
  @decorate_error α msg p cb n = fail n (Dlist.lazyOfList [msg ()]) :=
  decorate_errors_fail h

theorem decorate_error_success (h : p cb n = done n' a) : @decorate_error α msg p cb n = done n' a :=
  decorate_errors_success h

@[simp]
theorem decorate_errors_eq_done : @decorate_errors α msgs p cb n = done n' a ↔ p cb n = done n' a :=
  by 
    cases h : p cb n <;> simp [decorate_errors, h]

@[simp]
theorem decorate_error_eq_done : @decorate_error α msg p cb n = done n' a ↔ p cb n = done n' a :=
  decorate_errors_eq_done

@[simp]
theorem decorate_errors_eq_fail :
  @decorate_errors α msgs p cb n = fail n' err ↔
    n = n' ∧ err = Dlist.lazyOfList (msgs ()) ∧ ∃ np err', p cb n = fail np err' :=
  by 
    cases h : p cb n <;> simp [decorate_errors, h, eq_comm]

@[simp]
theorem decorate_error_eq_fail :
  @decorate_error α msg p cb n = fail n' err ↔
    n = n' ∧ err = Dlist.lazyOfList [msg ()] ∧ ∃ np err', p cb n = fail np err' :=
  decorate_errors_eq_fail

@[simp]
theorem return_eq_pure : @return Parser _ _ a = pure a :=
  rfl

theorem pure_eq_done : @pure Parser _ _ a = fun _ n => done n a :=
  rfl

@[simp]
theorem pure_ne_fail : (pure a : Parser α) cb n ≠ fail n' err :=
  by 
    simp [pure_eq_done]

section Bind

variable(f : α → Parser β)

@[simp]
theorem bind_eq_bind : p.bind f = p >>= f :=
  rfl

variable{f}

@[simp]
theorem bind_eq_done : (p >>= f) cb n = done n' b ↔ ∃ (np : ℕ)(a : α), p cb n = done np a ∧ f a cb np = done n' b :=
  by 
    cases hp : p cb n <;> simp [hp, ←bind_eq_bind, Parser.bind, and_assoc]

@[simp]
theorem bind_eq_fail :
  (p >>= f) cb n = fail n' err ↔
    p cb n = fail n' err ∨ ∃ (np : ℕ)(a : α), p cb n = done np a ∧ f a cb np = fail n' err :=
  by 
    cases hp : p cb n <;> simp [hp, ←bind_eq_bind, Parser.bind, and_assoc]

@[simp]
theorem and_then_eq_bind {α β : Type} {m : Type → Type} [Monadₓ m] (a : m α) (b : m β) : a >> b = a >>= fun _ => b :=
  rfl

theorem and_then_fail : (p >> return ()) cb n = ParseResult.fail n' err ↔ p cb n = fail n' err :=
  by 
    simp [pure_eq_done]

theorem and_then_success : (p >> return ()) cb n = ParseResult.done n' () ↔ ∃ a, p cb n = done n' a :=
  by 
    simp [pure_eq_done]

end Bind

section Map

variable{f : α → β}

@[simp]
theorem map_eq_done : (f <$> p) cb n = done n' b ↔ ∃ a : α, p cb n = done n' a ∧ f a = b :=
  by 
    cases hp : p cb n <;> simp [←IsLawfulMonad.bind_pure_comp_eq_map, hp, and_assoc, pure_eq_done]

@[simp]
theorem map_eq_fail : (f <$> p) cb n = fail n' err ↔ p cb n = fail n' err :=
  by 
    simp [←bind_pure_comp_eq_map, pure_eq_done]

@[simp]
theorem map_const_eq_done {b'} : (b <$ p) cb n = done n' b' ↔ ∃ a : α, p cb n = done n' a ∧ b = b' :=
  by 
    simp [map_const_eq]

@[simp]
theorem map_const_eq_fail : (b <$ p) cb n = fail n' err ↔ p cb n = fail n' err :=
  by 
    simp only [map_const_eq, map_eq_fail]

theorem map_const_rev_eq_done {b'} : (p $> b) cb n = done n' b' ↔ ∃ a : α, p cb n = done n' a ∧ b = b' :=
  map_const_eq_done

theorem map_rev_const_eq_fail : (p $> b) cb n = fail n' err ↔ p cb n = fail n' err :=
  map_const_eq_fail

end Map

@[simp]
theorem orelse_eq_orelse : p.orelse q = (p <|> q) :=
  rfl

@[simp]
theorem orelse_eq_done :
  (p <|> q) cb n = done n' a ↔ p cb n = done n' a ∨ q cb n = done n' a ∧ ∃ err, p cb n = fail n err :=
  by 
    cases' hp : p cb n with np resp np errp
    ·
      simp [hp, ←orelse_eq_orelse, Parser.orelse]
    ·
      byCases' hn : np = n
      ·
        cases' hq : q cb n with nq resq nq errq
        ·
          simp [hp, hn, hq, ←orelse_eq_orelse, Parser.orelse]
        ·
          rcases lt_trichotomyₓ nq n with (H | rfl | H) <;>
            first |
              simp [hp, hn, hq, H, not_lt_of_lt H, lt_irreflₓ, ←orelse_eq_orelse, Parser.orelse]|
              simp [hp, hn, hq, lt_irreflₓ, ←orelse_eq_orelse, Parser.orelse]
      ·
        simp [hp, hn, ←orelse_eq_orelse, Parser.orelse]

@[simp]
theorem orelse_eq_fail_eq :
  (p <|> q) cb n = fail n err ↔
    (p cb n = fail n err ∧ ∃ nq errq, n < nq ∧ q cb n = fail nq errq) ∨
      ∃ errp errq, p cb n = fail n errp ∧ q cb n = fail n errq ∧ errp ++ errq = err :=
  by 
    cases' hp : p cb n with np resp np errp
    ·
      simp [hp, ←orelse_eq_orelse, Parser.orelse]
    ·
      byCases' hn : np = n
      ·
        cases' hq : q cb n with nq resq nq errq
        ·
          simp [hp, hn, hq, ←orelse_eq_orelse, Parser.orelse]
        ·
          rcases lt_trichotomyₓ nq n with (H | rfl | H) <;>
            first |
              simp [hp, hq, hn, ←orelse_eq_orelse, Parser.orelse, H, ne_of_gtₓ H, ne_of_ltₓ H, not_lt_of_lt H]|
              simp [hp, hq, hn, ←orelse_eq_orelse, Parser.orelse, lt_irreflₓ]
      ·
        simp [hp, hn, ←orelse_eq_orelse, Parser.orelse]

theorem orelse_eq_fail_not_mono_lt (hn : n' < n) :
  (p <|> q) cb n = fail n' err ↔ p cb n = fail n' err ∨ q cb n = fail n' err ∧ ∃ errp, p cb n = fail n errp :=
  by 
    cases' hp : p cb n with np resp np errp
    ·
      simp [hp, ←orelse_eq_orelse, Parser.orelse]
    ·
      byCases' h : np = n
      ·
        cases' hq : q cb n with nq resq nq errq
        ·
          simp [hp, h, hn, hq, ne_of_gtₓ hn, ←orelse_eq_orelse, Parser.orelse]
        ·
          rcases lt_trichotomyₓ nq n with (H | H | H)
          ·
            simp [hp, hq, h, H, ne_of_gtₓ hn, not_lt_of_lt H, ←orelse_eq_orelse, Parser.orelse]
          ·
            simp [hp, hq, h, H, ne_of_gtₓ hn, lt_irreflₓ, ←orelse_eq_orelse, Parser.orelse]
          ·
            simp [hp, hq, h, H, ne_of_gtₓ (hn.trans H), ←orelse_eq_orelse, Parser.orelse]
      ·
        simp [hp, h, ←orelse_eq_orelse, Parser.orelse]

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem orelse_eq_fail_of_mono_ne
[q.mono]
(hn : «expr ≠ »(n, n')) : «expr ↔ »(«expr = »(«expr <|> »(p, q) cb n, fail n' err), «expr = »(p cb n, fail n' err)) :=
begin
  cases [expr hp, ":", expr p cb n] ["with", ident np, ident resp, ident np, ident errp],
  { simp [] [] [] ["[", expr hp, ",", "<-", expr orelse_eq_orelse, ",", expr parser.orelse, "]"] [] [] },
  { by_cases [expr h, ":", expr «expr = »(np, n)],
    { cases [expr hq, ":", expr q cb n] ["with", ident nq, ident resq, ident nq, ident errq],
      { simp [] [] [] ["[", expr hp, ",", expr h, ",", expr hn, ",", expr hq, ",", expr hn, ",", "<-", expr orelse_eq_orelse, ",", expr parser.orelse, "]"] [] [] },
      { have [] [":", expr «expr ≤ »(n, nq)] [":=", expr mono.of_fail hq],
        rcases [expr eq_or_lt_of_le this, "with", ident rfl, "|", ident H],
        { simp [] [] [] ["[", expr hp, ",", expr hq, ",", expr h, ",", expr hn, ",", expr lt_irrefl, ",", "<-", expr orelse_eq_orelse, ",", expr parser.orelse, "]"] [] [] },
        { simp [] [] [] ["[", expr hp, ",", expr hq, ",", expr h, ",", expr hn, ",", expr H, ",", "<-", expr orelse_eq_orelse, ",", expr parser.orelse, "]"] [] [] } } },
    { simp [] [] [] ["[", expr hp, ",", expr h, ",", "<-", expr orelse_eq_orelse, ",", expr parser.orelse, "]"] [] [] } }
end

@[simp]
theorem failure_eq_failure : @Parser.failure α = failure :=
  rfl

@[simp]
theorem failure_def : (failure : Parser α) cb n = fail n Dlist.empty :=
  rfl

theorem not_failure_eq_done : ¬(failure : Parser α) cb n = done n' a :=
  by 
    simp 

theorem failure_eq_fail : (failure : Parser α) cb n = fail n' err ↔ n = n' ∧ err = Dlist.empty :=
  by 
    simp [eq_comm]

theorem seq_eq_done {f : Parser (α → β)} {p : Parser α} :
  (f<*>p) cb n = done n' b ↔ ∃ (nf : ℕ)(f' : α → β)(a : α), f cb n = done nf f' ∧ p cb nf = done n' a ∧ f' a = b :=
  by 
    simp [seq_eq_bind_mapₓ]

theorem seq_eq_fail {f : Parser (α → β)} {p : Parser α} :
  (f<*>p) cb n = fail n' err ↔
    f cb n = fail n' err ∨ ∃ (nf : ℕ)(f' : α → β), f cb n = done nf f' ∧ p cb nf = fail n' err :=
  by 
    simp [seq_eq_bind_mapₓ]

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem seq_left_eq_done
{p : parser α}
{q : parser β} : «expr ↔ »(«expr = »(«expr <* »(p, q) cb n, done n' a), «expr∃ , »((np : exprℕ())
  (b : β), «expr ∧ »(«expr = »(p cb n, done np a), «expr = »(q cb np, done n' b)))) :=
begin
  have [] [":", expr ∀
   p
   q : exprℕ() → α → exprProp(), «expr ↔ »(«expr∃ , »((np : exprℕ())
     (x : α), «expr ∧ »(p np x, «expr ∧ »(q np x, «expr = »(x, a)))), «expr∃ , »((np : exprℕ()), «expr ∧ »(p np a, q np a)))] [":=", expr λ
   _ _, ⟨λ ⟨np, x, hp, hq, rfl⟩, ⟨np, hp, hq⟩, λ ⟨np, hp, hq⟩, ⟨np, a, hp, hq, rfl⟩⟩],
  simp [] [] [] ["[", expr seq_left_eq, ",", expr seq_eq_done, ",", expr map_eq_done, ",", expr this, "]"] [] []
end

theorem seq_left_eq_fail {p : Parser α} {q : Parser β} :
  (p <* q) cb n = fail n' err ↔ p cb n = fail n' err ∨ ∃ (np : ℕ)(a : α), p cb n = done np a ∧ q cb np = fail n' err :=
  by 
    simp [seq_left_eq, seq_eq_fail]

theorem seq_right_eq_done {p : Parser α} {q : Parser β} :
  (p *> q) cb n = done n' b ↔ ∃ (np : ℕ)(a : α), p cb n = done np a ∧ q cb np = done n' b :=
  by 
    simp [seq_right_eq, seq_eq_done, map_eq_done, And.comm, And.assoc]

theorem seq_right_eq_fail {p : Parser α} {q : Parser β} :
  (p *> q) cb n = fail n' err ↔ p cb n = fail n' err ∨ ∃ (np : ℕ)(a : α), p cb n = done np a ∧ q cb np = fail n' err :=
  by 
    simp [seq_right_eq, seq_eq_fail]

theorem mmap_eq_done {f : α → Parser β} {a : α} {l : List α} {b : β} {l' : List β} :
  (a :: l).mmap f cb n = done n' (b :: l') ↔ ∃ np : ℕ, f a cb n = done np b ∧ l.mmap f cb np = done n' l' :=
  by 
    simp [mmap, And.comm, And.assoc, And.left_comm, pure_eq_done]

theorem mmap'_eq_done {f : α → Parser β} {a : α} {l : List α} :
  (a :: l).mmap' f cb n = done n' () ↔ ∃ (np : ℕ)(b : β), f a cb n = done np b ∧ l.mmap' f cb np = done n' () :=
  by 
    simp [mmap']

theorem guard_eq_done {p : Prop} [Decidable p] {u : Unit} : @guardₓ Parser _ p _ cb n = done n' u ↔ p ∧ n = n' :=
  by 
    byCases' hp : p <;> simp [guardₓ, hp, pure_eq_done]

theorem guard_eq_fail {p : Prop} [Decidable p] :
  @guardₓ Parser _ p _ cb n = fail n' err ↔ ¬p ∧ n = n' ∧ err = Dlist.empty :=
  by 
    byCases' hp : p <;> simp [guardₓ, hp, eq_comm, pure_eq_done]

namespace Mono

variable{sep : Parser Unit}

instance pure : mono (pure a) :=
  ⟨fun _ _ =>
      by 
        simp [pure_eq_done]⟩

instance bind {f : α → Parser β} [p.mono] [∀ a, (f a).mono] : (p >>= f).mono :=
  by 
    constructor 
    intro cb n 
    cases hx : (p >>= f) cb n
    ·
      obtain ⟨n', a, h, h'⟩ := bind_eq_done.mp hx 
      refine' le_transₓ (of_done h) _ 
      simpa [h'] using of_done h'
    ·
      obtain h | ⟨n', a, h, h'⟩ := bind_eq_fail.mp hx
      ·
        simpa [h] using of_fail h
      ·
        refine' le_transₓ (of_done h) _ 
        simpa [h'] using of_fail h'

instance and_then {q : Parser β} [p.mono] [q.mono] : (p >> q).mono :=
  mono.bind

instance map [p.mono] {f : α → β} : (f <$> p).mono :=
  mono.bind

instance seq {f : Parser (α → β)} [f.mono] [p.mono] : (f<*>p).mono :=
  mono.bind

instance mmap : ∀ {l : List α} {f : α → Parser β} [∀ a (_ : a ∈ l), (f a).mono], (l.mmap f).mono
| [], _, _ => mono.pure
| a :: l, f, h =>
  by 
    convert mono.bind
    ·
      exact h _ (List.mem_cons_selfₓ _ _)
    ·
      intro 
      convert mono.map 
      convert mmap 
      exact fun _ ha => h _ (List.mem_cons_of_memₓ _ ha)

instance mmap' : ∀ {l : List α} {f : α → Parser β} [∀ a (_ : a ∈ l), (f a).mono], (l.mmap' f).mono
| [], _, _ => mono.pure
| a :: l, f, h =>
  by 
    convert mono.and_then
    ·
      exact h _ (List.mem_cons_selfₓ _ _)
    ·
      convert mmap' 
      exact fun _ ha => h _ (List.mem_cons_of_memₓ _ ha)

instance failure : (failure : Parser α).mono :=
  ⟨by 
      simp [le_reflₓ]⟩

instance guardₓ {p : Prop} [Decidable p] : mono (guardₓ p) :=
  ⟨by 
      byCases' h : p <;> simp [h, pure_eq_done, le_reflₓ]⟩

instance orelse [p.mono] [q.mono] : (p <|> q).mono :=
  by 
    constructor 
    intro cb n 
    cases' hx : (p <|> q) cb n with posx resx posx errx
    ·
      obtain h | ⟨h, -, -⟩ := orelse_eq_done.mp hx <;> simpa [h] using of_done h
    ·
      byCases' h : n = posx
      ·
        simp [hx, h]
      ·
        simp only [orelse_eq_fail_of_mono_ne h] at hx 
        exact of_fail hx

instance decorate_errors [p.mono] : (@decorate_errors α msgs p).mono :=
  by 
    constructor 
    intro cb n 
    cases h : p cb n
    ·
      simpa [decorate_errors, h] using of_done h
    ·
      simp [decorate_errors, h]

instance decorate_error [p.mono] : (@decorate_error α msg p).mono :=
  mono.decorate_errors

instance any_char : mono any_char :=
  by 
    constructor 
    intro cb n 
    byCases' h : n < cb.size <;> simp [any_char, h]

instance sat {p : Charₓ → Prop} [DecidablePred p] : mono (sat p) :=
  by 
    constructor 
    intro cb n 
    simp only [sat]
    splitIfs <;> simp 

instance eps : mono eps :=
  mono.pure

instance ch {c : Charₓ} : mono (ch c) :=
  mono.decorate_error

instance char_buf {s : CharBuffer} : mono (char_buf s) :=
  mono.decorate_error

instance one_of {cs : List Charₓ} : (one_of cs).mono :=
  mono.decorate_errors

instance one_of' {cs : List Charₓ} : (one_of' cs).mono :=
  mono.and_then

instance str {s : Stringₓ} : (str s).mono :=
  mono.decorate_error

instance remaining : remaining.mono :=
  ⟨fun _ _ => le_reflₓ _⟩

instance eof : eof.mono :=
  mono.decorate_error

instance foldr_core {f : α → β → β} {b : β} [p.mono] : ∀ {reps : ℕ}, (foldr_core f p b reps).mono
| 0 => mono.failure
| reps+1 =>
  by 
    convert mono.orelse
    ·
      convert mono.bind
      ·
        infer_instance
      ·
        exact fun _ => @mono.bind _ _ _ _ foldr_core _
    ·
      exact mono.pure

instance foldr {f : α → β → β} [p.mono] : mono (foldr f p b) :=
  ⟨fun _ _ =>
      by 
        convert mono.le (foldr_core f p b _) _ _ 
        exact mono.foldr_core⟩

instance foldl_core {f : α → β → α} {p : Parser β} [p.mono] : ∀ {a : α} {reps : ℕ}, (foldl_core f a p reps).mono
| _, 0 => mono.failure
| _, reps+1 =>
  by 
    convert mono.orelse
    ·
      convert mono.bind
      ·
        infer_instance
      ·
        exact fun _ => foldl_core
    ·
      exact mono.pure

instance foldl {f : α → β → α} {p : Parser β} [p.mono] : mono (foldl f a p) :=
  ⟨fun _ _ =>
      by 
        convert mono.le (foldl_core f a p _) _ _ 
        exact mono.foldl_core⟩

instance many [p.mono] : p.many.mono :=
  mono.foldr

instance many_char {p : Parser Charₓ} [p.mono] : p.many_char.mono :=
  mono.map

instance many' [p.mono] : p.many'.mono :=
  mono.and_then

instance many1 [p.mono] : p.many1.mono :=
  mono.seq

instance many_char1 {p : Parser Charₓ} [p.mono] : p.many_char1.mono :=
  mono.map

instance sep_by1 [p.mono] [sep.mono] : mono (sep_by1 sep p) :=
  mono.seq

instance sep_by [p.mono] [hs : sep.mono] : mono (sep_by sep p) :=
  mono.orelse

theorem fix_core {F : Parser α → Parser α} (hF : ∀ (p : Parser α), p.mono → (F p).mono) :
  ∀ (max_depth : ℕ), mono (fix_core F max_depth)
| 0 => mono.failure
| max_depth+1 => hF _ (fix_core _)

instance digit : digit.mono :=
  mono.decorate_error

instance Nat : Nat.mono :=
  mono.decorate_error

theorem fix {F : Parser α → Parser α} (hF : ∀ (p : Parser α), p.mono → (F p).mono) : mono (fix F) :=
  ⟨fun _ _ =>
      by 
        convert mono.le (Parser.fixCore F _) _ _ 
        exact fix_core hF _⟩

end Mono

@[simp]
theorem orelse_pure_eq_fail : (p <|> pure a) cb n = fail n' err ↔ p cb n = fail n' err ∧ n ≠ n' :=
  by 
    byCases' hn : n = n'
    ·
      simp [hn, pure_eq_done]
    ·
      simp [orelse_eq_fail_of_mono_ne, hn]

end DefnLemmas

section Done

variable{α β : Type}{cb : CharBuffer}{n n' : ℕ}{a a' : α}{b : β}{c : Charₓ}{u : Unit}{err : Dlist Stringₓ}

theorem any_char_eq_done : any_char cb n = done n' c ↔ ∃ hn : n < cb.size, (n' = n+1) ∧ cb.read ⟨n, hn⟩ = c :=
  by 
    simpRw [any_char]
    splitIfs with h <;> simp [h, eq_comm]

theorem any_char_eq_fail : any_char cb n = fail n' err ↔ n = n' ∧ err = Dlist.empty ∧ cb.size ≤ n :=
  by 
    simpRw [any_char]
    splitIfs with h <;> simp [←not_ltₓ, h, eq_comm]

theorem sat_eq_done {p : Charₓ → Prop} [DecidablePred p] :
  sat p cb n = done n' c ↔ ∃ hn : n < cb.size, p c ∧ (n' = n+1) ∧ cb.read ⟨n, hn⟩ = c :=
  by 
    byCases' hn : n < cb.size
    ·
      byCases' hp : p (cb.read ⟨n, hn⟩)
      ·
        simp only [sat, hn, hp, dif_pos, if_true, exists_prop_of_true]
        split 
        ·
          rintro ⟨rfl, rfl⟩
          simp [hp]
        ·
          rintro ⟨-, rfl, rfl⟩
          simp 
      ·
        simp only [sat, hn, hp, dif_pos, false_iffₓ, not_and, exists_prop_of_true, if_false]
        rintro H - rfl 
        exact hp H
    ·
      simp [sat, hn]

theorem sat_eq_fail {p : Charₓ → Prop} [DecidablePred p] :
  sat p cb n = fail n' err ↔ n = n' ∧ err = Dlist.empty ∧ ∀ (h : n < cb.size), ¬p (cb.read ⟨n, h⟩) :=
  by 
    dsimp only [sat]
    splitIfs <;> simp [eq_comm]

theorem eps_eq_done : eps cb n = done n' u ↔ n = n' :=
  by 
    simp [eps, pure_eq_done]

theorem ch_eq_done : ch c cb n = done n' u ↔ ∃ hn : n < cb.size, (n' = n+1) ∧ cb.read ⟨n, hn⟩ = c :=
  by 
    simp [ch, eps_eq_done, sat_eq_done, And.comm, @eq_comm _ n']

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem char_buf_eq_done
{cb' : char_buffer} : «expr ↔ »(«expr = »(char_buf cb' cb n, done n' u), «expr ∧ »(«expr = »(«expr + »(n, cb'.size), n'), «expr <+: »(cb'.to_list, cb.to_list.drop n))) :=
begin
  simp [] [] ["only"] ["[", expr char_buf, ",", expr decorate_error_eq_done, ",", expr ne.def, ",", "<-", expr buffer.length_to_list, "]"] [] [],
  induction [expr cb'.to_list] [] ["with", ident hd, ident tl, ident hl] ["generalizing", ident cb, ident n, ident n'],
  { simp [] [] [] ["[", expr pure_eq_done, ",", expr mmap'_eq_done, ",", "-", ident buffer.length_to_list, ",", expr list.nil_prefix, "]"] [] [] },
  { simp [] [] ["only"] ["[", expr ch_eq_done, ",", expr and.comm, ",", expr and.assoc, ",", expr and.left_comm, ",", expr hl, ",", expr mmap', ",", expr and_then_eq_bind, ",", expr bind_eq_done, ",", expr list.length, ",", expr exists_and_distrib_left, ",", expr exists_const, "]"] [] [],
    split,
    { rintro ["⟨", ident np, ",", ident h, ",", ident rfl, ",", ident rfl, ",", ident hn, ",", ident rfl, "⟩"],
      simp [] [] ["only"] ["[", expr add_comm, ",", expr add_left_comm, ",", expr h, ",", expr true_and, ",", expr eq_self_iff_true, ",", expr and_true, "]"] [] [],
      have [] [":", expr «expr < »(n, cb.to_list.length)] [":=", expr by simpa [] [] [] [] [] ["using", expr hn]],
      rwa ["[", "<-", expr buffer.nth_le_to_list _ this, ",", "<-", expr list.cons_nth_le_drop_succ this, ",", expr list.prefix_cons_inj, "]"] [] },
    { rintro ["⟨", ident h, ",", ident rfl, "⟩"],
      by_cases [expr hn, ":", expr «expr < »(n, cb.size)],
      { have [] [":", expr «expr < »(n, cb.to_list.length)] [":=", expr by simpa [] [] [] [] [] ["using", expr hn]],
        rw ["[", "<-", expr list.cons_nth_le_drop_succ this, ",", expr list.cons_prefix_iff, "]"] ["at", ident h],
        use ["[", expr «expr + »(n, 1), ",", expr h.right, "]"],
        simpa [] [] [] ["[", expr buffer.nth_le_to_list, ",", expr add_comm, ",", expr add_left_comm, ",", expr add_assoc, ",", expr hn, "]"] [] ["using", expr h.left.symm] },
      { have [] [":", expr «expr ≤ »(cb.to_list.length, n)] [":=", expr by simpa [] [] [] [] [] ["using", expr hn]],
        rw [expr list.drop_eq_nil_of_le this] ["at", ident h],
        simpa [] [] [] [] [] ["using", expr h] } } }
end

theorem one_of_eq_done {cs : List Charₓ} :
  one_of cs cb n = done n' c ↔ ∃ hn : n < cb.size, c ∈ cs ∧ (n' = n+1) ∧ cb.read ⟨n, hn⟩ = c :=
  by 
    simp [one_of, sat_eq_done]

theorem one_of'_eq_done {cs : List Charₓ} :
  one_of' cs cb n = done n' u ↔ ∃ hn : n < cb.size, cb.read ⟨n, hn⟩ ∈ cs ∧ n' = n+1 :=
  by 
    simp only [one_of', one_of_eq_done, eps_eq_done, And.comm, and_then_eq_bind, bind_eq_done, exists_eq_left,
      exists_and_distrib_left]
    split 
    ·
      rintro ⟨c, hc, rfl, hn, rfl⟩
      exact ⟨rfl, hn, hc⟩
    ·
      rintro ⟨rfl, hn, hc⟩
      exact ⟨cb.read ⟨n, hn⟩, hc, rfl, hn, rfl⟩

theorem str_eq_char_buf (s : Stringₓ) : str s = char_buf s.to_list.to_buffer :=
  by 
    ext cb n 
    rw [str, char_buf]
    congr
    ·
      simp [Buffer.toString, Stringₓ.as_string_inv_to_list]
    ·
      simp 

theorem str_eq_done {s : Stringₓ} : str s cb n = done n' u ↔ (n+s.length) = n' ∧ s.to_list <+: cb.to_list.drop n :=
  by 
    simp [str_eq_char_buf, char_buf_eq_done]

theorem remaining_eq_done {r : ℕ} : remaining cb n = done n' r ↔ n = n' ∧ cb.size - n = r :=
  by 
    simp [remaining]

theorem remaining_ne_fail : remaining cb n ≠ fail n' err :=
  by 
    simp [remaining]

theorem eof_eq_done {u : Unit} : eof cb n = done n' u ↔ n = n' ∧ cb.size ≤ n :=
  by 
    simp [eof, guard_eq_done, remaining_eq_done, tsub_eq_zero_iff_le, and_comm, and_assoc]

@[simp]
theorem foldr_core_zero_eq_done {f : α → β → β} {p : Parser α} {b' : β} : foldr_core f p b 0 cb n ≠ done n' b' :=
  by 
    simp [foldr_core]

theorem foldr_core_eq_done {f : α → β → β} {p : Parser α} {reps : ℕ} {b' : β} :
  foldr_core f p b (reps+1) cb n = done n' b' ↔
    (∃ (np : ℕ)(a : α)(xs : β), p cb n = done np a ∧ foldr_core f p b reps cb np = done n' xs ∧ f a xs = b') ∨
      n = n' ∧
        b = b' ∧
          ∃ err,
            p cb n = fail n err ∨ ∃ (np : ℕ)(a : α), p cb n = done np a ∧ foldr_core f p b reps cb np = fail n err :=
  by 
    simp [foldr_core, And.comm, And.assoc, pure_eq_done]

@[simp]
theorem foldr_core_zero_eq_fail {f : α → β → β} {p : Parser α} {err : Dlist Stringₓ} :
  foldr_core f p b 0 cb n = fail n' err ↔ n = n' ∧ err = Dlist.empty :=
  by 
    simp [foldr_core, eq_comm]

theorem foldr_core_succ_eq_fail {f : α → β → β} {p : Parser α} {reps : ℕ} {err : Dlist Stringₓ} :
  foldr_core f p b (reps+1) cb n = fail n' err ↔
    n ≠ n' ∧
      (p cb n = fail n' err ∨ ∃ (np : ℕ)(a : α), p cb n = done np a ∧ foldr_core f p b reps cb np = fail n' err) :=
  by 
    simp [foldr_core, and_comm]

theorem foldr_eq_done {f : α → β → β} {p : Parser α} {b' : β} :
  foldr f p b cb n = done n' b' ↔
    (∃ (np : ℕ)(a : α)(x : β), p cb n = done np a ∧ foldr_core f p b (cb.size - n) cb np = done n' x ∧ f a x = b') ∨
      n = n' ∧
        b = b' ∧
          ∃ err,
            p cb n = ParseResult.fail n err ∨
              ∃ (np : ℕ)(x : α), p cb n = done np x ∧ foldr_core f p b (cb.size - n) cb np = fail n err :=
  by 
    simp [foldr, foldr_core_eq_done]

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem foldr_eq_fail_iff_mono_at_end
{f : α → β → β}
{p : parser α}
{err : dlist string}
[p.mono]
(hc : «expr ≤ »(cb.size, n)) : «expr ↔ »(«expr = »(foldr f p b cb n, fail n' err), «expr ∧ »(«expr < »(n, n'), «expr ∨ »(«expr = »(p cb n, fail n' err), «expr∃ , »((a : α), «expr ∧ »(«expr = »(p cb n, done n' a), «expr = »(err, dlist.empty)))))) :=
begin
  have [] [":", expr «expr = »(«expr - »(cb.size, n), 0)] [":=", expr tsub_eq_zero_iff_le.mpr hc],
  simp [] [] ["only"] ["[", expr foldr, ",", expr foldr_core_succ_eq_fail, ",", expr this, ",", expr and.left_comm, ",", expr foldr_core_zero_eq_fail, ",", expr ne_iff_lt_iff_le, ",", expr exists_and_distrib_right, ",", expr exists_eq_left, ",", expr and.congr_left_iff, ",", expr exists_and_distrib_left, "]"] [] [],
  rintro ["(", ident h, "|", "⟨", "⟨", ident a, ",", ident h, "⟩", ",", ident rfl, "⟩", ")"],
  { exact [expr mono.of_fail h] },
  { exact [expr mono.of_done h] }
end

theorem foldr_eq_fail {f : α → β → β} {p : Parser α} {err : Dlist Stringₓ} :
  foldr f p b cb n = fail n' err ↔
    n ≠ n' ∧
      (p cb n = fail n' err ∨
        ∃ (np : ℕ)(a : α), p cb n = done np a ∧ foldr_core f p b (cb.size - n) cb np = fail n' err) :=
  by 
    simp [foldr, foldr_core_succ_eq_fail]

@[simp]
theorem foldl_core_zero_eq_done {f : β → α → β} {p : Parser α} {b' : β} :
  foldl_core f b p 0 cb n = done n' b' ↔ False :=
  by 
    simp [foldl_core]

theorem foldl_core_eq_done {f : β → α → β} {p : Parser α} {reps : ℕ} {b' : β} :
  foldl_core f b p (reps+1) cb n = done n' b' ↔
    (∃ (np : ℕ)(a : α), p cb n = done np a ∧ foldl_core f (f b a) p reps cb np = done n' b') ∨
      n = n' ∧
        b = b' ∧
          ∃ err,
            p cb n = fail n err ∨
              ∃ (np : ℕ)(a : α), p cb n = done np a ∧ foldl_core f (f b a) p reps cb np = fail n err :=
  by 
    simp [foldl_core, And.assoc, pure_eq_done]

@[simp]
theorem foldl_core_zero_eq_fail {f : β → α → β} {p : Parser α} {err : Dlist Stringₓ} :
  foldl_core f b p 0 cb n = fail n' err ↔ n = n' ∧ err = Dlist.empty :=
  by 
    simp [foldl_core, eq_comm]

theorem foldl_core_succ_eq_fail {f : β → α → β} {p : Parser α} {reps : ℕ} {err : Dlist Stringₓ} :
  foldl_core f b p (reps+1) cb n = fail n' err ↔
    n ≠ n' ∧
      (p cb n = fail n' err ∨
        ∃ (np : ℕ)(a : α), p cb n = done np a ∧ foldl_core f (f b a) p reps cb np = fail n' err) :=
  by 
    simp [foldl_core, and_comm]

theorem foldl_eq_done {f : β → α → β} {p : Parser α} {b' : β} :
  foldl f b p cb n = done n' b' ↔
    (∃ (np : ℕ)(a : α), p cb n = done np a ∧ foldl_core f (f b a) p (cb.size - n) cb np = done n' b') ∨
      n = n' ∧
        b = b' ∧
          ∃ err,
            p cb n = fail n err ∨
              ∃ (np : ℕ)(a : α), p cb n = done np a ∧ foldl_core f (f b a) p (cb.size - n) cb np = fail n err :=
  by 
    simp [foldl, foldl_core_eq_done]

theorem foldl_eq_fail {f : β → α → β} {p : Parser α} {err : Dlist Stringₓ} :
  foldl f b p cb n = fail n' err ↔
    n ≠ n' ∧
      (p cb n = fail n' err ∨
        ∃ (np : ℕ)(a : α), p cb n = done np a ∧ foldl_core f (f b a) p (cb.size - n) cb np = fail n' err) :=
  by 
    simp [foldl, foldl_core_succ_eq_fail]

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem foldl_eq_fail_iff_mono_at_end
{f : β → α → β}
{p : parser α}
{err : dlist string}
[p.mono]
(hc : «expr ≤ »(cb.size, n)) : «expr ↔ »(«expr = »(foldl f b p cb n, fail n' err), «expr ∧ »(«expr < »(n, n'), «expr ∨ »(«expr = »(p cb n, fail n' err), «expr∃ , »((a : α), «expr ∧ »(«expr = »(p cb n, done n' a), «expr = »(err, dlist.empty)))))) :=
begin
  have [] [":", expr «expr = »(«expr - »(cb.size, n), 0)] [":=", expr tsub_eq_zero_iff_le.mpr hc],
  simp [] [] ["only"] ["[", expr foldl, ",", expr foldl_core_succ_eq_fail, ",", expr this, ",", expr and.left_comm, ",", expr ne_iff_lt_iff_le, ",", expr exists_eq_left, ",", expr exists_and_distrib_right, ",", expr and.congr_left_iff, ",", expr exists_and_distrib_left, ",", expr foldl_core_zero_eq_fail, "]"] [] [],
  rintro ["(", ident h, "|", "⟨", "⟨", ident a, ",", ident h, "⟩", ",", ident rfl, "⟩", ")"],
  { exact [expr mono.of_fail h] },
  { exact [expr mono.of_done h] }
end

theorem many_eq_done_nil {p : Parser α} :
  many p cb n = done n' (@List.nil α) ↔
    n = n' ∧
      ∃ err,
        p cb n = fail n err ∨
          ∃ (np : ℕ)(a : α), p cb n = done np a ∧ foldr_core List.cons p [] (cb.size - n) cb np = fail n err :=
  by 
    simp [many, foldr_eq_done]

theorem many_eq_done {p : Parser α} {x : α} {xs : List α} :
  many p cb n = done n' (x :: xs) ↔
    ∃ np : ℕ, p cb n = done np x ∧ foldr_core List.cons p [] (cb.size - n) cb np = done n' xs :=
  by 
    simp [many, foldr_eq_done, And.comm, And.assoc, And.left_comm]

theorem many_eq_fail {p : Parser α} {err : Dlist Stringₓ} :
  many p cb n = fail n' err ↔
    n ≠ n' ∧
      (p cb n = fail n' err ∨
        ∃ (np : ℕ)(a : α), p cb n = done np a ∧ foldr_core List.cons p [] (cb.size - n) cb np = fail n' err) :=
  by 
    simp [many, foldr_eq_fail]

theorem many_char_eq_done_empty {p : Parser Charₓ} :
  many_char p cb n = done n' Stringₓ.empty ↔
    n = n' ∧
      ∃ err,
        p cb n = fail n err ∨
          ∃ (np : ℕ)(c : Charₓ), p cb n = done np c ∧ foldr_core List.cons p [] (cb.size - n) cb np = fail n err :=
  by 
    simp [many_char, many_eq_done_nil, map_eq_done, List.as_string_eq]

theorem many_char_eq_done_not_empty {p : Parser Charₓ} {s : Stringₓ} (h : s ≠ "") :
  many_char p cb n = done n' s ↔
    ∃ np : ℕ,
      p cb n = done np s.head ∧
        foldr_core List.cons p List.nil (Buffer.size cb - n) cb np = done n' (s.popn 1).toList :=
  by 
    simp [many_char, List.as_string_eq, Stringₓ.to_list_nonempty h, many_eq_done]

theorem many_char_eq_many_of_to_list {p : Parser Charₓ} {s : Stringₓ} :
  many_char p cb n = done n' s ↔ many p cb n = done n' s.to_list :=
  by 
    simp [many_char, List.as_string_eq]

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem many'_eq_done
{p : parser α} : «expr ↔ »(«expr = »(many' p cb n, done n' u), «expr ∨ »(«expr = »(many p cb n, done n' «expr[ , ]»([])), «expr∃ , »((np : exprℕ())
   (a : α)
   (l : list α), «expr ∧ »(«expr = »(many p cb n, done n' [«expr :: »/«expr :: »/«expr :: »](a, l)), «expr ∧ »(«expr = »(p cb n, done np a), «expr = »(foldr_core list.cons p «expr[ , ]»([]) «expr - »(buffer.size cb, n) cb np, done n' l)))))) :=
begin
  simp [] [] ["only"] ["[", expr many', ",", expr eps_eq_done, ",", expr many, ",", expr foldr, ",", expr and_then_eq_bind, ",", expr exists_and_distrib_right, ",", expr bind_eq_done, ",", expr exists_eq_right, "]"] [] [],
  split,
  { rintro ["⟨", "_", "|", "⟨", ident hd, ",", ident tl, "⟩", ",", ident hl, "⟩"],
    { exact [expr or.inl hl] },
    { have [ident hl2] [] [":=", expr hl],
      simp [] [] ["only"] ["[", expr foldr_core_eq_done, ",", expr or_false, ",", expr exists_and_distrib_left, ",", expr and_false, ",", expr false_and, ",", expr exists_eq_right_right, "]"] [] ["at", ident hl],
      obtain ["⟨", ident np, ",", ident hp, ",", ident h, "⟩", ":=", expr hl],
      refine [expr or.inr ⟨np, _, _, hl2, hp, h⟩] } },
  { rintro ["(", ident h, "|", "⟨", ident np, ",", ident a, ",", ident l, ",", ident hp, ",", ident h, "⟩", ")"],
    { exact [expr ⟨«expr[ , ]»([]), h⟩] },
    { refine [expr ⟨[«expr :: »/«expr :: »/«expr :: »](a, l), hp⟩] } }
end

@[simp]
theorem many1_ne_done_nil {p : Parser α} : many1 p cb n ≠ done n' [] :=
  by 
    simp [many1, seq_eq_done]

theorem many1_eq_done {p : Parser α} {l : List α} :
  many1 p cb n = done n' (a :: l) ↔ ∃ np : ℕ, p cb n = done np a ∧ many p cb np = done n' l :=
  by 
    simp [many1, seq_eq_done, map_eq_done]

theorem many1_eq_fail {p : Parser α} {err : Dlist Stringₓ} :
  many1 p cb n = fail n' err ↔
    p cb n = fail n' err ∨ ∃ (np : ℕ)(a : α), p cb n = done np a ∧ many p cb np = fail n' err :=
  by 
    simp [many1, seq_eq_fail]

@[simp]
theorem many_char1_ne_empty {p : Parser Charₓ} : many_char1 p cb n ≠ done n' "" :=
  by 
    simp [many_char1, ←Stringₓ.nil_as_string_eq_empty]

theorem many_char1_eq_done {p : Parser Charₓ} {s : Stringₓ} (h : s ≠ "") :
  many_char1 p cb n = done n' s ↔ ∃ np : ℕ, p cb n = done np s.head ∧ many_char p cb np = done n' (s.popn 1) :=
  by 
    simp [many_char1, List.as_string_eq, Stringₓ.to_list_nonempty h, many1_eq_done, many_char_eq_many_of_to_list]

@[simp]
theorem sep_by1_ne_done_nil {sep : Parser Unit} {p : Parser α} : sep_by1 sep p cb n ≠ done n' [] :=
  by 
    simp [sep_by1, seq_eq_done]

theorem sep_by1_eq_done {sep : Parser Unit} {p : Parser α} {l : List α} :
  sep_by1 sep p cb n = done n' (a :: l) ↔ ∃ np : ℕ, p cb n = done np a ∧ (sep >> p).many cb np = done n' l :=
  by 
    simp [sep_by1, seq_eq_done]

theorem sep_by_eq_done_nil {sep : Parser Unit} {p : Parser α} :
  sep_by sep p cb n = done n' [] ↔ n = n' ∧ ∃ err, sep_by1 sep p cb n = fail n err :=
  by 
    simp [sep_by, pure_eq_done]

@[simp]
theorem fix_core_ne_done_zero {F : Parser α → Parser α} : fix_core F 0 cb n ≠ done n' a :=
  by 
    simp [fix_core]

theorem fix_core_eq_done {F : Parser α → Parser α} {max_depth : ℕ} :
  fix_core F (max_depth+1) cb n = done n' a ↔ F (fix_core F max_depth) cb n = done n' a :=
  by 
    simp [fix_core]

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem digit_eq_done
{k : exprℕ()} : «expr ↔ »(«expr = »(digit cb n, done n' k), «expr∃ , »((hn : «expr < »(n, cb.size)), «expr ∧ »(«expr = »(n', «expr + »(n, 1)), «expr ∧ »(«expr ≤ »(k, 9), «expr ∧ »(«expr = »(«expr - »((cb.read ⟨n, hn⟩).to_nat, '0'.to_nat), k), «expr ∧ »(«expr ≤ »('0', cb.read ⟨n, hn⟩), «expr ≤ »(cb.read ⟨n, hn⟩, '9'))))))) :=
begin
  have [ident c9] [":", expr «expr = »(«expr - »('9'.to_nat, '0'.to_nat), 9)] [":=", expr rfl],
  have [ident l09] [":", expr «expr ≤ »('0'.to_nat, '9'.to_nat)] [":=", expr exprdec_trivial()],
  have [ident le_iff_le] [":", expr ∀
   {c c' : char}, «expr ↔ »(«expr ≤ »(c, c'), «expr ≤ »(c.to_nat, c'.to_nat))] [":=", expr λ _ _, iff.rfl],
  split,
  { simp [] [] ["only"] ["[", expr digit, ",", expr sat_eq_done, ",", expr pure_eq_done, ",", expr decorate_error_eq_done, ",", expr bind_eq_done, ",", "<-", expr c9, "]"] [] [],
    rintro ["⟨", ident np, ",", ident c, ",", "⟨", ident hn, ",", "⟨", ident ge0, ",", ident le9, "⟩", ",", ident rfl, ",", ident rfl, "⟩", ",", ident rfl, ",", ident rfl, "⟩"],
    simpa [] [] [] ["[", expr hn, ",", expr ge0, ",", expr le9, ",", expr true_and, ",", expr and_true, ",", expr eq_self_iff_true, ",", expr exists_prop_of_true, ",", expr tsub_le_tsub_iff_right, ",", expr l09, "]"] [] ["using", expr le_iff_le.mp le9] },
  { simp [] [] ["only"] ["[", expr digit, ",", expr sat_eq_done, ",", expr pure_eq_done, ",", expr decorate_error_eq_done, ",", expr bind_eq_done, ",", "<-", expr c9, ",", expr le_iff_le, "]"] [] [],
    rintro ["⟨", ident hn, ",", ident rfl, ",", "-", ",", ident rfl, ",", ident ge0, ",", ident le9, "⟩"],
    use ["[", expr «expr + »(n, 1), ",", expr cb.read ⟨n, hn⟩, "]"],
    simp [] [] [] ["[", expr hn, ",", expr ge0, ",", expr le9, "]"] [] [] }
end

theorem digit_eq_fail :
  digit cb n = fail n' err ↔
    n = n' ∧ err = Dlist.ofList ["<digit>"] ∧ ∀ (h : n < cb.size), ¬(fun c => '0' ≤ c ∧ c ≤ '9') (cb.read ⟨n, h⟩) :=
  by 
    simp [digit, sat_eq_fail]

end Done

namespace Static

variable{α β :
    Type}{p q :
    Parser
      α}{msgs :
    Thunkₓ
      (List
        Stringₓ)}{msg : Thunkₓ Stringₓ}{cb : CharBuffer}{n' n : ℕ}{err : Dlist Stringₓ}{a : α}{b : β}{sep : Parser Unit}

theorem not_of_ne (h : p cb n = done n' a) (hne : n ≠ n') : ¬static p :=
  by 
    intro 
    exact hne (of_done h)

instance pure : static (pure a) :=
  ⟨fun _ _ _ _ =>
      by 
        simpRw [pure_eq_done]
        rw [And.comm]
        simp ⟩

instance bind {f : α → Parser β} [p.static] [∀ a, (f a).Static] : (p >>= f).Static :=
  ⟨fun _ _ _ _ =>
      by 
        rw [bind_eq_done]
        rintro ⟨_, _, hp, hf⟩
        exact trans (of_done hp) (of_done hf)⟩

instance and_then {q : Parser β} [p.static] [q.static] : (p >> q).Static :=
  static.bind

instance map [p.static] {f : α → β} : (f <$> p).Static :=
  ⟨fun _ _ _ _ =>
      by 
        simpRw [map_eq_done]
        rintro ⟨_, hp, _⟩
        exact of_done hp⟩

instance seq {f : Parser (α → β)} [f.static] [p.static] : (f<*>p).Static :=
  static.bind

instance mmap : ∀ {l : List α} {f : α → Parser β} [∀ a, (f a).Static], (l.mmap f).Static
| [], _, _ => static.pure
| a :: l, _, h =>
  by 
    convert static.bind
    ·
      exact h _
    ·
      intro 
      convert static.bind
      ·
        convert mmap 
        exact h
      ·
        exact fun _ => static.pure

instance mmap' : ∀ {l : List α} {f : α → Parser β} [∀ a, (f a).Static], (l.mmap' f).Static
| [], _, _ => static.pure
| a :: l, _, h =>
  by 
    convert static.and_then
    ·
      exact h _
    ·
      convert mmap' 
      exact h

instance failure : @Parser.Static α failure :=
  ⟨fun _ _ _ _ =>
      by 
        simp ⟩

instance guardₓ {p : Prop} [Decidable p] : static (guardₓ p) :=
  ⟨fun _ _ _ _ =>
      by 
        simp [guard_eq_done]⟩

instance orelse [p.static] [q.static] : (p <|> q).Static :=
  ⟨fun _ _ _ _ =>
      by 
        simpRw [orelse_eq_done]
        rintro (h | ⟨h, -⟩) <;> exact of_done h⟩

instance decorate_errors [p.static] : (@decorate_errors α msgs p).Static :=
  ⟨fun _ _ _ _ =>
      by 
        rw [decorate_errors_eq_done]
        exact of_done⟩

instance decorate_error [p.static] : (@decorate_error α msg p).Static :=
  static.decorate_errors

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem any_char : «expr¬ »(static any_char) :=
begin
  have [] [":", expr «expr = »(any_char "s".to_char_buffer 0, done 1 's')] [],
  { have [] [":", expr «expr < »(0, "s".to_char_buffer.size)] [":=", expr exprdec_trivial()],
    simpa [] [] [] ["[", expr any_char_eq_done, ",", expr this, "]"] [] [] },
  exact [expr not_of_ne this zero_ne_one]
end

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sat_iff {p : char → exprProp()} [decidable_pred p] : «expr ↔ »(static (sat p), ∀ c, «expr¬ »(p c)) :=
begin
  split,
  { introI [],
    intros [ident c, ident hc],
    have [] [":", expr «expr = »(sat p «expr[ , ]»([c]).to_buffer 0, done 1 c)] [":=", expr by simp [] [] [] ["[", expr sat_eq_done, ",", expr hc, "]"] [] []],
    exact [expr zero_ne_one (of_done this)] },
  { contrapose ["!"] [],
    simp [] [] ["only"] ["[", expr iff, ",", expr sat_eq_done, ",", expr and_imp, ",", expr exists_prop, ",", expr exists_and_distrib_right, ",", expr exists_and_distrib_left, ",", expr exists_imp_distrib, ",", expr not_forall, "]"] [] [],
    rintros ["_", "_", "_", ident a, ident h, ident hne, ident rfl, ident hp, "-"],
    exact [expr ⟨a, hp⟩] }
end

instance sat : static (sat fun _ => False) :=
  by 
    apply sat_iff.mpr 
    simp 

instance eps : static eps :=
  static.pure

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ch (c : char) : «expr¬ »(static (ch c)) :=
begin
  have [] [":", expr «expr = »(ch c «expr[ , ]»([c]).to_buffer 0, done 1 ())] [],
  { have [] [":", expr «expr < »(0, «expr[ , ]»([c]).to_buffer.size)] [":=", expr exprdec_trivial()],
    simp [] [] [] ["[", expr ch_eq_done, ",", expr this, "]"] [] [] },
  exact [expr not_of_ne this zero_ne_one]
end

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem char_buf_iff {cb' : char_buffer} : «expr ↔ »(static (char_buf cb'), «expr = »(cb', buffer.nil)) :=
begin
  rw ["<-", expr buffer.size_eq_zero_iff] [],
  have [] [":", expr «expr = »(char_buf cb' cb' 0, done cb'.size ())] [":=", expr by simp [] [] [] ["[", expr char_buf_eq_done, "]"] [] []],
  cases [expr hc, ":", expr cb'.size] ["with", ident n],
  { simp [] [] ["only"] ["[", expr eq_self_iff_true, ",", expr iff_true, "]"] [] [],
    exact [expr ⟨λ _ _ _ _ h, by simpa [] [] [] ["[", expr hc, "]"] [] ["using", expr (char_buf_eq_done.mp h).left]⟩] },
  { rw [expr hc] ["at", ident this],
    simpa [] [] [] ["[", expr nat.succ_ne_zero, "]"] [] ["using", expr not_of_ne this (nat.succ_ne_zero n).symm] }
end

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem one_of_iff {cs : list char} : «expr ↔ »(static (one_of cs), «expr = »(cs, «expr[ , ]»([]))) :=
begin
  cases [expr cs] ["with", ident hd, ident tl],
  { simp [] [] [] ["[", expr one_of, ",", expr static.decorate_errors, "]"] [] [] },
  { have [] [":", expr «expr = »(one_of [«expr :: »/«expr :: »/«expr :: »](hd, tl) [«expr :: »/«expr :: »/«expr :: »](hd, tl).to_buffer 0, done 1 hd)] [],
    { simp [] [] [] ["[", expr one_of_eq_done, "]"] [] [] },
    simpa [] [] [] [] [] ["using", expr not_of_ne this zero_ne_one] }
end

instance one_of : static (one_of []) :=
  by 
    apply one_of_iff.mpr 
    rfl

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem one_of'_iff {cs : list char} : «expr ↔ »(static (one_of' cs), «expr = »(cs, «expr[ , ]»([]))) :=
begin
  cases [expr cs] ["with", ident hd, ident tl],
  { simp [] [] [] ["[", expr one_of', ",", expr static.bind, "]"] [] [] },
  { have [] [":", expr «expr = »(one_of' [«expr :: »/«expr :: »/«expr :: »](hd, tl) [«expr :: »/«expr :: »/«expr :: »](hd, tl).to_buffer 0, done 1 ())] [],
    { simp [] [] [] ["[", expr one_of'_eq_done, "]"] [] [] },
    simpa [] [] [] [] [] ["using", expr not_of_ne this zero_ne_one] }
end

instance one_of' : static (one_of []) :=
  by 
    apply one_of_iff.mpr 
    rfl

theorem str_iff {s : Stringₓ} : static (str s) ↔ s = "" :=
  by 
    simp [str_eq_char_buf, char_buf_iff, ←Stringₓ.to_list_inj, Buffer.ext_iff]

instance remaining : remaining.Static :=
  ⟨fun _ _ _ _ h => (remaining_eq_done.mp h).left⟩

instance eof : eof.Static :=
  static.decorate_error

instance foldr_core {f : α → β → β} [p.static] : ∀ {b : β} {reps : ℕ}, (foldr_core f p b reps).Static
| _, 0 => static.failure
| _, reps+1 =>
  by 
    simpRw [Parser.foldrCore]
    convert static.orelse
    ·
      convert static.bind
      ·
        infer_instance
      ·
        intro 
        convert static.bind
        ·
          exact foldr_core
        ·
          infer_instance
    ·
      exact static.pure

instance foldr {f : α → β → β} [p.static] : static (foldr f p b) :=
  ⟨fun _ _ _ _ =>
      by 
        dsimp [foldr]
        exact of_done⟩

instance foldl_core {f : α → β → α} {p : Parser β} [p.static] : ∀ {a : α} {reps : ℕ}, (foldl_core f a p reps).Static
| _, 0 => static.failure
| _, reps+1 =>
  by 
    convert static.orelse
    ·
      convert static.bind
      ·
        infer_instance
      ·
        exact fun _ => foldl_core
    ·
      exact static.pure

instance foldl {f : α → β → α} {p : Parser β} [p.static] : static (foldl f a p) :=
  ⟨fun _ _ _ _ =>
      by 
        dsimp [foldl]
        exact of_done⟩

instance many [p.static] : p.many.static :=
  static.foldr

instance many_char {p : Parser Charₓ} [p.static] : p.many_char.static :=
  static.map

instance many' [p.static] : p.many'.static :=
  static.and_then

instance many1 [p.static] : p.many1.static :=
  static.seq

instance many_char1 {p : Parser Charₓ} [p.static] : p.many_char1.static :=
  static.map

instance sep_by1 [p.static] [sep.static] : static (sep_by1 sep p) :=
  static.seq

instance sep_by [p.static] [sep.static] : static (sep_by sep p) :=
  static.orelse

theorem fix_core {F : Parser α → Parser α} (hF : ∀ (p : Parser α), p.static → (F p).Static) :
  ∀ (max_depth : ℕ), static (fix_core F max_depth)
| 0 => static.failure
| max_depth+1 => hF _ (fix_core _)

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem digit : «expr¬ »(digit.static) :=
begin
  have [] [":", expr «expr = »(digit "1".to_char_buffer 0, done 1 1)] [],
  { have [] [":", expr «expr < »(0, "s".to_char_buffer.size)] [":=", expr exprdec_trivial()],
    simpa [] [] [] ["[", expr this, "]"] [] [] },
  exact [expr not_of_ne this zero_ne_one]
end

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nat : «expr¬ »(nat.static) :=
begin
  have [] [":", expr «expr = »(nat "1".to_char_buffer 0, done 1 1)] [],
  { have [] [":", expr «expr < »(0, "s".to_char_buffer.size)] [":=", expr exprdec_trivial()],
    simpa [] [] [] ["[", expr this, "]"] [] [] },
  exact [expr not_of_ne this zero_ne_one]
end

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fix {F : parser α → parser α} (hF : ∀ p : parser α, p.static → (F p).static) : static (fix F) :=
⟨λ cb n _ _ h, by { haveI [] [] [":=", expr fix_core hF «expr + »(«expr - »(cb.size, n), 1)],
   dsimp [] ["[", expr fix, "]"] [] ["at", ident h],
   exact [expr static.of_done h] }⟩

end Static

namespace Bounded

variable{α β : Type}{msgs : Thunkₓ (List Stringₓ)}{msg : Thunkₓ Stringₓ}

variable{p q : Parser α}{cb : CharBuffer}{n n' : ℕ}{err : Dlist Stringₓ}

variable{a : α}{b : β}

theorem done_of_unbounded (h : ¬p.bounded) : ∃ (cb : CharBuffer)(n n' : ℕ)(a : α), p cb n = done n' a ∧ cb.size ≤ n :=
  by 
    contrapose! h 
    constructor 
    intro cb n hn 
    cases hp : p cb n
    ·
      exact absurd hn (h _ _ _ _ hp).not_le
    ·
      simp [hp]

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pure : «expr¬ »(bounded (pure a)) :=
begin
  introI [],
  have [] [":", expr «expr = »((pure a : parser α) buffer.nil 0, done 0 a)] [":=", expr by simp [] [] [] ["[", expr pure_eq_done, "]"] [] []],
  exact [expr absurd (bounded.of_done this) (lt_irrefl _)]
end

instance bind {f : α → Parser β} [p.bounded] : (p >>= f).Bounded :=
  by 
    constructor 
    intro cb n hn 
    obtain ⟨_, _, hp⟩ := bounded.exists p hn 
    simp [hp]

instance and_then {q : Parser β} [p.bounded] : (p >> q).Bounded :=
  bounded.bind

instance map [p.bounded] {f : α → β} : (f <$> p).Bounded :=
  bounded.bind

instance seq {f : Parser (α → β)} [f.bounded] : (f<*>p).Bounded :=
  bounded.bind

instance mmap {a : α} {l : List α} {f : α → Parser β} [∀ a, (f a).Bounded] : ((a :: l).mmap f).Bounded :=
  bounded.bind

instance mmap' {a : α} {l : List α} {f : α → Parser β} [∀ a, (f a).Bounded] : ((a :: l).mmap' f).Bounded :=
  bounded.and_then

instance failure : @Parser.Bounded α failure :=
  ⟨by 
      simp ⟩

theorem guard_iff {p : Prop} [Decidable p] : Bounded (guardₓ p) ↔ ¬p :=
  by 
    simpa [guardₓ, apply_ite Bounded, pure, failure] using fun _ => bounded.failure

instance orelse [p.bounded] [q.bounded] : (p <|> q).Bounded :=
  by 
    constructor 
    intro cb n hn 
    cases' hx : (p <|> q) cb n with posx resx posx errx
    ·
      obtain h | ⟨h, -, -⟩ := orelse_eq_done.mp hx <;> exact absurd hn (of_done h).not_le
    ·
      simp 

instance decorate_errors [p.bounded] : (@decorate_errors α msgs p).Bounded :=
  by 
    constructor 
    intro _ _ 
    simpa using bounded.exists p

theorem decorate_errors_iff : (@Parser.decorateErrors α msgs p).Bounded ↔ p.bounded :=
  by 
    split 
    ·
      intro 
      constructor 
      intro _ _ hn 
      obtain ⟨_, _, h⟩ := bounded.exists (@Parser.decorateErrors α msgs p) hn 
      simp [decorate_errors_eq_fail] at h 
      exact h.right.right
    ·
      intro 
      constructor 
      intro _ _ hn 
      obtain ⟨_, _, h⟩ := bounded.exists p hn 
      simp [h]

instance decorate_error [p.bounded] : (@decorate_error α msg p).Bounded :=
  bounded.decorate_errors

theorem decorate_error_iff : (@Parser.decorateError α msg p).Bounded ↔ p.bounded :=
  decorate_errors_iff

instance any_char : Bounded any_char :=
  ⟨fun cb n hn =>
      by 
        simp [any_char, hn]⟩

instance sat {p : Charₓ → Prop} [DecidablePred p] : Bounded (sat p) :=
  ⟨fun cb n hn =>
      by 
        simp [sat, hn]⟩

theorem eps : ¬Bounded eps :=
  pure

instance ch {c : Charₓ} : Bounded (ch c) :=
  bounded.decorate_error

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem char_buf_iff {cb' : char_buffer} : «expr ↔ »(bounded (char_buf cb'), «expr ≠ »(cb', buffer.nil)) :=
begin
  have [] [":", expr «expr ↔ »(«expr ≠ »(cb', buffer.nil), «expr ≠ »(cb'.to_list, «expr[ , ]»([])))] [":=", expr not_iff_not_of_iff ⟨λ
    h, by simp [] [] [] ["[", expr h, "]"] [] [], λ
    h, by simpa [] [] [] [] [] ["using", expr congr_arg list.to_buffer h]⟩],
  rw ["[", expr char_buf, ",", expr decorate_error_iff, ",", expr this, "]"] [],
  cases [expr cb'.to_list] [],
  { simp [] [] [] ["[", expr pure, ",", expr ch, "]"] [] [] },
  { simp [] [] ["only"] ["[", expr iff_true, ",", expr ne.def, ",", expr not_false_iff, "]"] [] [],
    apply_instance }
end

instance one_of {cs : List Charₓ} : (one_of cs).Bounded :=
  bounded.decorate_errors

instance one_of' {cs : List Charₓ} : (one_of' cs).Bounded :=
  bounded.and_then

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem str_iff {s : string} : «expr ↔ »((str s).bounded, «expr ≠ »(s, "")) :=
begin
  rw ["[", expr str, ",", expr decorate_error_iff, "]"] [],
  cases [expr hs, ":", expr s.to_list] [],
  { have [] [":", expr «expr = »(s, "")] [],
    { cases [expr s] [],
      rw ["[", expr string.to_list, "]"] ["at", ident hs],
      simpa [] [] [] ["[", expr hs, "]"] [] [] },
    simp [] [] [] ["[", expr pure, ",", expr this, "]"] [] [] },
  { have [] [":", expr «expr ≠ »(s, "")] [],
    { intro [ident H],
      simpa [] [] [] ["[", expr H, "]"] [] ["using", expr hs] },
    simp [] [] ["only"] ["[", expr this, ",", expr iff_true, ",", expr ne.def, ",", expr not_false_iff, "]"] [] [],
    apply_instance }
end

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem remaining : «expr¬ »(remaining.bounded) :=
begin
  introI [],
  have [] [":", expr «expr = »(remaining buffer.nil 0, done 0 0)] [":=", expr by simp [] [] [] ["[", expr remaining_eq_done, "]"] [] []],
  exact [expr absurd (bounded.of_done this) (lt_irrefl _)]
end

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eof : «expr¬ »(eof.bounded) :=
begin
  introI [],
  have [] [":", expr «expr = »(eof buffer.nil 0, done 0 ())] [":=", expr by simp [] [] [] ["[", expr eof_eq_done, "]"] [] []],
  exact [expr absurd (bounded.of_done this) (lt_irrefl _)]
end

section Fold

instance foldr_core_zero {f : α → β → β} : (foldr_core f p b 0).Bounded :=
  bounded.failure

instance foldl_core_zero {f : β → α → β} {b : β} : (foldl_core f b p 0).Bounded :=
  bounded.failure

variable{reps : ℕ}[hpb : p.bounded](he : ∀ cb n n' err, p cb n = fail n' err → n ≠ n')

include hpb he

theorem foldr_core {f : α → β → β} : (foldr_core f p b reps).Bounded :=
  by 
    cases reps
    ·
      exact bounded.foldr_core_zero 
    constructor 
    intro cb n hn 
    obtain ⟨np, errp, hp⟩ := bounded.exists p hn 
    simpa [foldr_core_succ_eq_fail, hp] using he cb n np errp

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem foldr {f : α → β → β} : bounded (foldr f p b) :=
begin
  constructor,
  intros [ident cb, ident n, ident hn],
  haveI [] [":", expr (parser.foldr_core f p b «expr + »(«expr - »(cb.size, n), 1)).bounded] [":=", expr foldr_core he],
  obtain ["⟨", ident np, ",", ident errp, ",", ident hp, "⟩", ":=", expr bounded.exists (parser.foldr_core f p b «expr + »(«expr - »(cb.size, n), 1)) hn],
  simp [] [] [] ["[", expr foldr, ",", expr hp, "]"] [] []
end

theorem foldl_core {f : β → α → β} : (foldl_core f b p reps).Bounded :=
  by 
    cases reps
    ·
      exact bounded.foldl_core_zero 
    constructor 
    intro cb n hn 
    obtain ⟨np, errp, hp⟩ := bounded.exists p hn 
    simpa [foldl_core_succ_eq_fail, hp] using he cb n np errp

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem foldl {f : β → α → β} : bounded (foldl f b p) :=
begin
  constructor,
  intros [ident cb, ident n, ident hn],
  haveI [] [":", expr (parser.foldl_core f b p «expr + »(«expr - »(cb.size, n), 1)).bounded] [":=", expr foldl_core he],
  obtain ["⟨", ident np, ",", ident errp, ",", ident hp, "⟩", ":=", expr bounded.exists (parser.foldl_core f b p «expr + »(«expr - »(cb.size, n), 1)) hn],
  simp [] [] [] ["[", expr foldl, ",", expr hp, "]"] [] []
end

theorem many : p.many.bounded :=
  foldr he

omit hpb

theorem many_char {pc : Parser Charₓ} [pc.bounded] (he : ∀ cb n n' err, pc cb n = fail n' err → n ≠ n') :
  pc.many_char.bounded :=
  by 
    convert bounded.map 
    exact many he

include hpb

theorem many' : p.many'.bounded :=
  by 
    convert bounded.and_then 
    exact many he

end Fold

instance many1 [p.bounded] : p.many1.bounded :=
  bounded.seq

instance many_char1 {p : Parser Charₓ} [p.bounded] : p.many_char1.bounded :=
  bounded.map

instance sep_by1 {sep : Parser Unit} [p.bounded] : Bounded (sep_by1 sep p) :=
  bounded.seq

theorem fix_core {F : Parser α → Parser α} (hF : ∀ (p : Parser α), p.bounded → (F p).Bounded) :
  ∀ (max_depth : ℕ), Bounded (fix_core F max_depth)
| 0 => bounded.failure
| max_depth+1 => hF _ (fix_core _)

instance digit : digit.Bounded :=
  bounded.decorate_error

instance Nat : Nat.Bounded :=
  bounded.decorate_error

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fix {F : parser α → parser α} (hF : ∀ p : parser α, p.bounded → (F p).bounded) : bounded (fix F) :=
begin
  constructor,
  intros [ident cb, ident n, ident hn],
  haveI [] [":", expr (parser.fix_core F «expr + »(«expr - »(cb.size, n), 1)).bounded] [":=", expr fix_core hF _],
  obtain ["⟨", ident np, ",", ident errp, ",", ident hp, "⟩", ":=", expr bounded.exists (parser.fix_core F «expr + »(«expr - »(cb.size, n), 1)) hn],
  simp [] [] [] ["[", expr fix, ",", expr hp, "]"] [] []
end

end Bounded

namespace Unfailing

variable{α β :
    Type}{p q :
    Parser
      α}{msgs :
    Thunkₓ
      (List
        Stringₓ)}{msg : Thunkₓ Stringₓ}{cb : CharBuffer}{n' n : ℕ}{err : Dlist Stringₓ}{a : α}{b : β}{sep : Parser Unit}

theorem of_bounded [p.bounded] : ¬unfailing p :=
  by 
    intro 
    cases h : p Buffer.nil 0
    ·
      simpa [lt_irreflₓ] using bounded.of_done h
    ·
      exact of_fail h

instance pure : unfailing (pure a) :=
  ⟨fun _ _ =>
      by 
        simp [pure_eq_done]⟩

instance bind {f : α → Parser β} [p.unfailing] [∀ a, (f a).Unfailing] : (p >>= f).Unfailing :=
  ⟨fun cb n =>
      by 
        obtain ⟨np, a, hp⟩ := exists_done p cb n 
        simpa [hp, And.comm, And.left_comm, And.assoc] using exists_done (f a) cb np⟩

instance and_then {q : Parser β} [p.unfailing] [q.unfailing] : (p >> q).Unfailing :=
  unfailing.bind

instance map [p.unfailing] {f : α → β} : (f <$> p).Unfailing :=
  unfailing.bind

instance seq {f : Parser (α → β)} [f.unfailing] [p.unfailing] : (f<*>p).Unfailing :=
  unfailing.bind

instance mmap {l : List α} {f : α → Parser β} [∀ a, (f a).Unfailing] : (l.mmap f).Unfailing :=
  by 
    constructor 
    induction' l with hd tl hl
    ·
      intros 
      simp [pure_eq_done]
    ·
      intros 
      obtain ⟨np, a, hp⟩ := exists_done (f hd) cb n 
      obtain ⟨n', b, hf⟩ := hl cb np 
      simp [hp, hf, And.comm, And.left_comm, And.assoc, pure_eq_done]

instance mmap' {l : List α} {f : α → Parser β} [∀ a, (f a).Unfailing] : (l.mmap' f).Unfailing :=
  by 
    constructor 
    induction' l with hd tl hl
    ·
      intros 
      simp [pure_eq_done]
    ·
      intros 
      obtain ⟨np, a, hp⟩ := exists_done (f hd) cb n 
      obtain ⟨n', b, hf⟩ := hl cb np 
      simp [hp, hf, And.comm, And.left_comm, And.assoc, pure_eq_done]

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem failure : «expr¬ »(@parser.unfailing α failure) :=
begin
  introI [ident h],
  have [] [":", expr «expr = »((failure : parser α) buffer.nil 0, fail 0 dlist.empty)] [":=", expr by simp [] [] [] [] [] []],
  exact [expr of_fail this]
end

instance guard_true : unfailing (guardₓ True) :=
  unfailing.pure

theorem guardₓ : ¬unfailing (guardₓ False) :=
  unfailing.failure

instance orelse [p.unfailing] : (p <|> q).Unfailing :=
  ⟨fun cb n =>
      by 
        obtain ⟨_, _, h⟩ := p.exists_done cb n 
        simp [success_iff, h]⟩

instance decorate_errors [p.unfailing] : (@decorate_errors α msgs p).Unfailing :=
  ⟨fun cb n =>
      by 
        obtain ⟨_, _, h⟩ := p.exists_done cb n 
        simp [success_iff, h]⟩

instance decorate_error [p.unfailing] : (@decorate_error α msg p).Unfailing :=
  unfailing.decorate_errors

instance any_char : conditionally_unfailing any_char :=
  ⟨fun _ _ hn =>
      by 
        simp [success_iff, any_char_eq_done, hn]⟩

theorem sat : conditionally_unfailing (sat fun _ => True) :=
  ⟨fun _ _ hn =>
      by 
        simp [success_iff, sat_eq_done, hn]⟩

instance eps : unfailing eps :=
  unfailing.pure

instance remaining : remaining.Unfailing :=
  ⟨fun _ _ =>
      by 
        simp [success_iff, remaining_eq_done]⟩

theorem foldr_core_zero {f : α → β → β} {b : β} : ¬(foldr_core f p b 0).Unfailing :=
  unfailing.failure

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance foldr_core_of_static
{f : α → β → β}
{b : β}
{reps : exprℕ()}
[p.static]
[p.unfailing] : (foldr_core f p b «expr + »(reps, 1)).unfailing :=
begin
  induction [expr reps] [] ["with", ident reps, ident hr] [],
  { constructor,
    intros [ident cb, ident n],
    obtain ["⟨", ident np, ",", ident a, ",", ident h, "⟩", ":=", expr p.exists_done cb n],
    simpa [] [] [] ["[", expr foldr_core_eq_done, ",", expr h, "]"] [] ["using", expr (static.of_done h).symm] },
  { constructor,
    haveI [] [] [":=", expr hr],
    intros [ident cb, ident n],
    obtain ["⟨", ident np, ",", ident a, ",", ident h, "⟩", ":=", expr p.exists_done cb n],
    have [] [":", expr «expr = »(n, np)] [":=", expr static.of_done h],
    subst [expr this],
    obtain ["⟨", ident np, ",", ident b', ",", ident hf, "⟩", ":=", expr exists_done (foldr_core f p b «expr + »(reps, 1)) cb n],
    have [] [":", expr «expr = »(n, np)] [":=", expr static.of_done hf],
    subst [expr this],
    refine [expr ⟨n, f a b', _⟩],
    rw [expr foldr_core_eq_done] [],
    simp [] [] [] ["[", expr h, ",", expr hf, ",", expr and.comm, ",", expr and.left_comm, ",", expr and.assoc, "]"] [] [] }
end

instance foldr_core_one_of_err_static {f : α → β → β} {b : β} [p.static] [p.err_static] :
  (foldr_core f p b 1).Unfailing :=
  by 
    constructor 
    intro cb n 
    cases h : p cb n
    ·
      simpa [foldr_core_eq_done, h] using (static.of_done h).symm
    ·
      simpa [foldr_core_eq_done, h] using (err_static.of_fail h).symm

theorem digit : ¬digit.Unfailing :=
  of_bounded

theorem Nat : ¬Nat.Unfailing :=
  of_bounded

end Unfailing

namespace ErrStatic

variable{α β :
    Type}{p q :
    Parser
      α}{msgs :
    Thunkₓ
      (List
        Stringₓ)}{msg : Thunkₓ Stringₓ}{cb : CharBuffer}{n' n : ℕ}{err : Dlist Stringₓ}{a : α}{b : β}{sep : Parser Unit}

theorem not_of_ne (h : p cb n = fail n' err) (hne : n ≠ n') : ¬err_static p :=
  by 
    intro 
    exact hne (of_fail h)

instance pure : err_static (pure a) :=
  ⟨fun _ _ _ _ =>
      by 
        simp [pure_eq_done]⟩

instance bind {f : α → Parser β} [p.static] [p.err_static] [∀ a, (f a).ErrStatic] : (p >>= f).ErrStatic :=
  ⟨fun cb n n' err =>
      by 
        rw [bind_eq_fail]
        rintro (hp | ⟨_, _, hp, hf⟩)
        ·
          exact of_fail hp
        ·
          exact trans (static.of_done hp) (of_fail hf)⟩

instance bind_of_unfailing {f : α → Parser β} [p.err_static] [∀ a, (f a).Unfailing] : (p >>= f).ErrStatic :=
  ⟨fun cb n n' err =>
      by 
        rw [bind_eq_fail]
        rintro (hp | ⟨_, _, hp, hf⟩)
        ·
          exact of_fail hp
        ·
          exact False.elim (unfailing.of_fail hf)⟩

instance and_then {q : Parser β} [p.static] [p.err_static] [q.err_static] : (p >> q).ErrStatic :=
  err_static.bind

instance and_then_of_unfailing {q : Parser β} [p.err_static] [q.unfailing] : (p >> q).ErrStatic :=
  err_static.bind_of_unfailing

instance map [p.err_static] {f : α → β} : (f <$> p).ErrStatic :=
  ⟨fun _ _ _ _ =>
      by 
        rw [map_eq_fail]
        exact of_fail⟩

instance seq {f : Parser (α → β)} [f.static] [f.err_static] [p.err_static] : (f<*>p).ErrStatic :=
  err_static.bind

instance seq_of_unfailing {f : Parser (α → β)} [f.err_static] [p.unfailing] : (f<*>p).ErrStatic :=
  err_static.bind_of_unfailing

instance mmap : ∀ {l : List α} {f : α → Parser β} [∀ a, (f a).Static] [∀ a, (f a).ErrStatic], (l.mmap f).ErrStatic
| [], _, _, _ => err_static.pure
| a :: l, _, h, h' =>
  by 
    convert err_static.bind
    ·
      exact h _
    ·
      exact h' _
    ·
      intro 
      convert err_static.bind
      ·
        convert static.mmap 
        exact h
      ·
        apply mmap
        ·
          exact h
        ·
          exact h'
      ·
        exact fun _ => err_static.pure

instance mmap_of_unfailing :
  ∀ {l : List α} {f : α → Parser β} [∀ a, (f a).Unfailing] [∀ a, (f a).ErrStatic], (l.mmap f).ErrStatic
| [], _, _, _ => err_static.pure
| a :: l, _, h, h' =>
  by 
    convert err_static.bind_of_unfailing
    ·
      exact h' _
    ·
      intro 
      convert unfailing.bind
      ·
        convert unfailing.mmap 
        exact h
      ·
        exact fun _ => unfailing.pure

instance mmap' : ∀ {l : List α} {f : α → Parser β} [∀ a, (f a).Static] [∀ a, (f a).ErrStatic], (l.mmap' f).ErrStatic
| [], _, _, _ => err_static.pure
| a :: l, _, h, h' =>
  by 
    convert err_static.and_then
    ·
      exact h _
    ·
      exact h' _
    ·
      convert mmap'
      ·
        exact h
      ·
        exact h'

instance mmap'_of_unfailing :
  ∀ {l : List α} {f : α → Parser β} [∀ a, (f a).Unfailing] [∀ a, (f a).ErrStatic], (l.mmap' f).ErrStatic
| [], _, _, _ => err_static.pure
| a :: l, _, h, h' =>
  by 
    convert err_static.and_then_of_unfailing
    ·
      exact h' _
    ·
      convert unfailing.mmap' 
      exact h

instance failure : @Parser.ErrStatic α failure :=
  ⟨fun _ _ _ _ h => (failure_eq_fail.mp h).left⟩

instance guardₓ {p : Prop} [Decidable p] : err_static (guardₓ p) :=
  ⟨fun _ _ _ _ h => (guard_eq_fail.mp h).right.left⟩

instance orelse [p.err_static] [q.mono] : (p <|> q).ErrStatic :=
  ⟨fun _ n n' _ =>
      by 
        byCases' hn : n = n'
        ·
          exact fun _ => hn
        ·
          rw [orelse_eq_fail_of_mono_ne hn]
          ·
            exact of_fail
          ·
            infer_instance⟩

instance decorate_errors : (@decorate_errors α msgs p).ErrStatic :=
  ⟨fun _ _ _ _ h => (decorate_errors_eq_fail.mp h).left⟩

instance decorate_error : (@decorate_error α msg p).ErrStatic :=
  err_static.decorate_errors

instance any_char : err_static any_char :=
  ⟨fun _ _ _ _ =>
      by 
        rw [any_char_eq_fail, And.comm]
        simp ⟩

instance sat_iff {p : Charₓ → Prop} [DecidablePred p] : err_static (sat p) :=
  ⟨fun _ _ _ _ h => (sat_eq_fail.mp h).left⟩

instance eps : err_static eps :=
  err_static.pure

instance ch (c : Charₓ) : err_static (ch c) :=
  err_static.decorate_error

instance char_buf {cb' : CharBuffer} : err_static (char_buf cb') :=
  err_static.decorate_error

instance one_of {cs : List Charₓ} : err_static (one_of cs) :=
  err_static.decorate_errors

instance one_of' {cs : List Charₓ} : err_static (one_of' cs) :=
  err_static.and_then_of_unfailing

instance str {s : Stringₓ} : err_static (str s) :=
  err_static.decorate_error

instance remaining : remaining.ErrStatic :=
  ⟨fun _ _ _ _ =>
      by 
        simp [remaining_ne_fail]⟩

instance eof : eof.ErrStatic :=
  err_static.decorate_error

theorem fix_core {F : Parser α → Parser α} (hF : ∀ (p : Parser α), p.err_static → (F p).ErrStatic) :
  ∀ (max_depth : ℕ), err_static (fix_core F max_depth)
| 0 => err_static.failure
| max_depth+1 => hF _ (fix_core _)

instance digit : digit.ErrStatic :=
  err_static.decorate_error

instance Nat : Nat.ErrStatic :=
  err_static.decorate_error

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fix {F : parser α → parser α} (hF : ∀ p : parser α, p.err_static → (F p).err_static) : err_static (fix F) :=
⟨λ cb n _ _ h, by { haveI [] [] [":=", expr fix_core hF «expr + »(«expr - »(cb.size, n), 1)],
   dsimp [] ["[", expr fix, "]"] [] ["at", ident h],
   exact [expr err_static.of_fail h] }⟩

end ErrStatic

namespace Step

variable{α β :
    Type}{p q :
    Parser
      α}{msgs :
    Thunkₓ
      (List
        Stringₓ)}{msg : Thunkₓ Stringₓ}{cb : CharBuffer}{n' n : ℕ}{err : Dlist Stringₓ}{a : α}{b : β}{sep : Parser Unit}

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem not_step_of_static_done
[static p]
(h : «expr∃ , »((cb n n' a), «expr = »(p cb n, done n' a))) : «expr¬ »(step p) :=
begin
  introI [],
  rcases [expr h, "with", "⟨", ident cb, ",", ident n, ",", ident n', ",", ident a, ",", ident h, "⟩"],
  have [ident hs] [] [":=", expr static.of_done h],
  simpa [] [] [] ["[", "<-", expr hs, "]"] [] ["using", expr of_done h]
end

theorem pure (a : α) : ¬step (pure a) :=
  by 
    apply not_step_of_static_done 
    simp [pure_eq_done]

instance bind {f : α → Parser β} [p.step] [∀ a, (f a).Static] : (p >>= f).step :=
  ⟨fun _ _ _ _ =>
      by 
        simpRw [bind_eq_done]
        rintro ⟨_, _, hp, hf⟩
        exact static.of_done hf ▸ of_done hp⟩

instance bind' {f : α → Parser β} [p.static] [∀ a, (f a).step] : (p >>= f).step :=
  ⟨fun _ _ _ _ =>
      by 
        simpRw [bind_eq_done]
        rintro ⟨_, _, hp, hf⟩
        rw [static.of_done hp]
        exact of_done hf⟩

instance and_then {q : Parser β} [p.step] [q.static] : (p >> q).step :=
  step.bind

instance and_then' {q : Parser β} [p.static] [q.step] : (p >> q).step :=
  step.bind'

instance map [p.step] {f : α → β} : (f <$> p).step :=
  ⟨fun _ _ _ _ =>
      by 
        simpRw [map_eq_done]
        rintro ⟨_, hp, _⟩
        exact of_done hp⟩

instance seq {f : Parser (α → β)} [f.step] [p.static] : (f<*>p).step :=
  step.bind

instance seq' {f : Parser (α → β)} [f.static] [p.step] : (f<*>p).step :=
  step.bind'

instance mmap {f : α → Parser β} [(f a).step] : ([a].mmap f).step :=
  by 
    convert step.bind
    ·
      infer_instance
    ·
      intro 
      convert static.bind
      ·
        exact static.pure
      ·
        exact fun _ => static.pure

instance mmap' {f : α → Parser β} [(f a).step] : ([a].mmap' f).step :=
  by 
    convert step.and_then
    ·
      infer_instance
    ·
      exact static.pure

instance failure : @Parser.Step α failure :=
  ⟨fun _ _ _ _ =>
      by 
        simp ⟩

theorem guard_true : ¬step (guardₓ True) :=
  pure _

instance guardₓ : step (guardₓ False) :=
  step.failure

instance orelse [p.step] [q.step] : (p <|> q).step :=
  ⟨fun _ _ _ _ =>
      by 
        simpRw [orelse_eq_done]
        rintro (h | ⟨h, -⟩) <;> exact of_done h⟩

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem decorate_errors_iff : «expr ↔ »((@parser.decorate_errors α msgs p).step, p.step) :=
begin
  split,
  { introI [],
    constructor,
    intros [ident cb, ident n, ident n', ident a, ident h],
    have [] [":", expr «expr = »(@parser.decorate_errors α msgs p cb n, done n' a)] [":=", expr by simpa [] [] [] [] [] ["using", expr h]],
    exact [expr of_done this] },
  { introI [],
    constructor,
    intros ["_", "_", "_", "_", ident h],
    rw [expr decorate_errors_eq_done] ["at", ident h],
    exact [expr of_done h] }
end

instance decorate_errors [p.step] : (@decorate_errors α msgs p).step :=
  ⟨fun _ _ _ _ =>
      by 
        rw [decorate_errors_eq_done]
        exact of_done⟩

theorem decorate_error_iff : (@Parser.decorateError α msg p).step ↔ p.step :=
  decorate_errors_iff

instance decorate_error [p.step] : (@decorate_error α msg p).step :=
  step.decorate_errors

instance any_char : step any_char :=
  by 
    constructor 
    intro cb n 
    simpRw [any_char_eq_done]
    rintro _ _ ⟨_, rfl, -⟩
    simp 

instance sat {p : Charₓ → Prop} [DecidablePred p] : step (sat p) :=
  by 
    constructor 
    intro cb n 
    simpRw [sat_eq_done]
    rintro _ _ ⟨_, _, rfl, -⟩
    simp 

theorem eps : ¬step eps :=
  step.pure ()

instance ch {c : Charₓ} : step (ch c) :=
  step.decorate_error

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem char_buf_iff {cb' : char_buffer} : «expr ↔ »((char_buf cb').step, «expr = »(cb'.size, 1)) :=
begin
  have [] [":", expr «expr = »(char_buf cb' cb' 0, done cb'.size ())] [":=", expr by simp [] [] [] ["[", expr char_buf_eq_done, "]"] [] []],
  split,
  { introI [],
    simpa [] [] [] [] [] ["using", expr of_done this] },
  { intro [ident h],
    constructor,
    intros [ident cb, ident n, ident n', "_"],
    rw ["[", expr char_buf_eq_done, ",", expr h, "]"] [],
    rintro ["⟨", ident rfl, ",", "-", "⟩"],
    refl }
end

instance one_of {cs : List Charₓ} : (one_of cs).step :=
  step.decorate_errors

instance one_of' {cs : List Charₓ} : (one_of' cs).step :=
  step.and_then

theorem str_iff {s : Stringₓ} : (str s).step ↔ s.length = 1 :=
  by 
    simp [str_eq_char_buf, char_buf_iff, ←Stringₓ.to_list_inj, Buffer.ext_iff]

theorem remaining : ¬remaining.step :=
  by 
    apply not_step_of_static_done 
    simp [remaining_eq_done]

theorem eof : ¬eof.step :=
  by 
    apply not_step_of_static_done 
    simp only [eof_eq_done, exists_eq_left', exists_const]
    use Buffer.nil, 0
    simp 

theorem fix_core {F : Parser α → Parser α} (hF : ∀ (p : Parser α), p.step → (F p).step) :
  ∀ (max_depth : ℕ), step (fix_core F max_depth)
| 0 => step.failure
| max_depth+1 => hF _ (fix_core _)

instance digit : digit.step :=
  step.decorate_error

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fix {F : parser α → parser α} (hF : ∀ p : parser α, p.step → (F p).step) : step (fix F) :=
⟨λ cb n _ _ h, by { haveI [] [] [":=", expr fix_core hF «expr + »(«expr - »(cb.size, n), 1)],
   dsimp [] ["[", expr fix, "]"] [] ["at", ident h],
   exact [expr of_done h] }⟩

end Step

section Step

variable{α β :
    Type}{p q :
    Parser
      α}{msgs :
    Thunkₓ
      (List
        Stringₓ)}{msg : Thunkₓ Stringₓ}{cb : CharBuffer}{n' n : ℕ}{err : Dlist Stringₓ}{a : α}{b : β}{sep : Parser Unit}

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem many1_eq_done_iff_many_eq_done
[p.step]
[p.bounded]
{x : α}
{xs : list α} : «expr ↔ »(«expr = »(many1 p cb n, done n' [«expr :: »/«expr :: »/«expr :: »](x, xs)), «expr = »(many p cb n, done n' [«expr :: »/«expr :: »/«expr :: »](x, xs))) :=
begin
  induction [expr hx, ":", expr [«expr :: »/«expr :: »/«expr :: »](x, xs)] [] ["with", ident hd, ident tl, ident IH] ["generalizing", ident x, ident xs, ident n, ident n'],
  { simpa [] [] [] [] [] ["using", expr hx] },
  split,
  { simp [] [] ["only"] ["[", expr many1_eq_done, ",", expr and_imp, ",", expr exists_imp_distrib, "]"] [] [],
    intros [ident np, ident hp, ident hm],
    have [] [":", expr «expr = »(np, «expr + »(n, 1))] [":=", expr step.of_done hp],
    have [ident hn] [":", expr «expr < »(n, cb.size)] [":=", expr bounded.of_done hp],
    subst [expr this],
    obtain ["⟨", ident k, ",", ident hk, "⟩", ":", expr «expr∃ , »((k), «expr = »(«expr - »(cb.size, n), «expr + »(k, 1))), ":=", expr nat.exists_eq_succ_of_ne_zero (ne_of_gt (tsub_pos_of_lt hn))],
    cases [expr k] [],
    { cases [expr tl] []; simpa [] [] [] ["[", expr many_eq_done_nil, ",", expr nat.sub_succ, ",", expr hk, ",", expr many_eq_done, ",", expr hp, ",", expr foldr_core_eq_done, "]"] [] ["using", expr hm] },
    cases [expr tl] ["with", ident hd', ident tl'],
    { simpa [] [] [] ["[", expr many_eq_done_nil, ",", expr nat.sub_succ, ",", expr hk, ",", expr many_eq_done, ",", expr hp, ",", expr foldr_core_eq_done, "]"] [] ["using", expr hm] },
    { rw ["<-", expr @IH hd' tl'] ["at", ident hm],
      swap,
      refl,
      simp [] [] ["only"] ["[", expr many1_eq_done, ",", expr many, ",", expr foldr, "]"] [] ["at", ident hm],
      obtain ["⟨", ident np, ",", ident hp', ",", ident hf, "⟩", ":=", expr hm],
      have [] [":", expr «expr = »(np, «expr + »(«expr + »(n, 1), 1))] [":=", expr step.of_done hp'],
      subst [expr this],
      simpa [] [] [] ["[", expr nat.sub_succ, ",", expr many_eq_done, ",", expr hp, ",", expr hk, ",", expr foldr_core_eq_done, ",", expr hp', "]"] [] ["using", expr hf] } },
  { simp [] [] ["only"] ["[", expr many_eq_done, ",", expr many1_eq_done, ",", expr and_imp, ",", expr exists_imp_distrib, "]"] [] [],
    intros [ident np, ident hp, ident hm],
    have [] [":", expr «expr = »(np, «expr + »(n, 1))] [":=", expr step.of_done hp],
    have [ident hn] [":", expr «expr < »(n, cb.size)] [":=", expr bounded.of_done hp],
    subst [expr this],
    obtain ["⟨", ident k, ",", ident hk, "⟩", ":", expr «expr∃ , »((k), «expr = »(«expr - »(cb.size, n), «expr + »(k, 1))), ":=", expr nat.exists_eq_succ_of_ne_zero (ne_of_gt (tsub_pos_of_lt hn))],
    cases [expr k] [],
    { cases [expr tl] []; simpa [] [] [] ["[", expr many_eq_done_nil, ",", expr nat.sub_succ, ",", expr hk, ",", expr many_eq_done, ",", expr hp, ",", expr foldr_core_eq_done, "]"] [] ["using", expr hm] },
    cases [expr tl] ["with", ident hd', ident tl'],
    { simpa [] [] [] ["[", expr many_eq_done_nil, ",", expr nat.sub_succ, ",", expr hk, ",", expr many_eq_done, ",", expr hp, ",", expr foldr_core_eq_done, "]"] [] ["using", expr hm] },
    { simp [] [] [] ["[", expr hp, "]"] [] [],
      rw ["<-", expr @IH hd' tl' «expr + »(n, 1) n'] [],
      swap,
      refl,
      rw ["[", expr hk, ",", expr foldr_core_eq_done, ",", expr or.comm, "]"] ["at", ident hm],
      obtain ["(", ident hm, "|", "⟨", ident np, ",", ident hd', ",", ident tl', ",", ident hp', ",", ident hf, ",", ident hm, "⟩", ")", ":=", expr hm],
      { simpa [] [] [] [] [] ["using", expr hm] },
      simp [] [] ["only"] [] [] ["at", ident hm],
      obtain ["⟨", ident rfl, ",", ident rfl, "⟩", ":=", expr hm],
      have [] [":", expr «expr = »(np, «expr + »(«expr + »(n, 1), 1))] [":=", expr step.of_done hp'],
      subst [expr this],
      simp [] [] [] ["[", expr nat.sub_succ, ",", expr many, ",", expr many1_eq_done, ",", expr hp, ",", expr hk, ",", expr foldr_core_eq_done, ",", expr hp', ",", "<-", expr hf, ",", expr foldr, "]"] [] [] } }
end

end Step

namespace Prog

variable{α β :
    Type}{p q :
    Parser
      α}{msgs :
    Thunkₓ
      (List
        Stringₓ)}{msg : Thunkₓ Stringₓ}{cb : CharBuffer}{n' n : ℕ}{err : Dlist Stringₓ}{a : α}{b : β}{sep : Parser Unit}

instance (priority := 100)of_step [step p] : prog p :=
  ⟨fun _ _ _ _ h =>
      by 
        rw [step.of_done h]
        exact Nat.lt_succ_selfₓ _⟩

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pure (a : α) : «expr¬ »(prog (pure a)) :=
begin
  introI [ident h],
  have [] [":", expr «expr = »((pure a : parser α) buffer.nil 0, done 0 a)] [":=", expr by simp [] [] [] ["[", expr pure_eq_done, "]"] [] []],
  replace [ident this] [":", expr «expr < »(0, 0)] [":=", expr prog.of_done this],
  exact [expr lt_irrefl _ this]
end

instance bind {f : α → Parser β} [p.prog] [∀ a, (f a).mono] : (p >>= f).Prog :=
  ⟨fun _ _ _ _ =>
      by 
        simpRw [bind_eq_done]
        rintro ⟨_, _, hp, hf⟩
        exact lt_of_lt_of_leₓ (of_done hp) (mono.of_done hf)⟩

instance and_then {q : Parser β} [p.prog] [q.mono] : (p >> q).Prog :=
  prog.bind

instance map [p.prog] {f : α → β} : (f <$> p).Prog :=
  ⟨fun _ _ _ _ =>
      by 
        simpRw [map_eq_done]
        rintro ⟨_, hp, _⟩
        exact of_done hp⟩

instance seq {f : Parser (α → β)} [f.prog] [p.mono] : (f<*>p).Prog :=
  prog.bind

instance mmap {l : List α} {f : α → Parser β} [(f a).Prog] [∀ a, (f a).mono] : ((a :: l).mmap f).Prog :=
  by 
    constructor 
    simp only [and_imp, bind_eq_done, return_eq_pure, mmap, exists_imp_distrib, pure_eq_done]
    rintro _ _ _ _ _ _ h _ _ hp rfl rfl 
    exact lt_of_lt_of_leₓ (of_done h) (mono.of_done hp)

instance mmap' {l : List α} {f : α → Parser β} [(f a).Prog] [∀ a, (f a).mono] : ((a :: l).mmap' f).Prog :=
  by 
    constructor 
    simp only [and_imp, bind_eq_done, mmap', exists_imp_distrib, and_then_eq_bind]
    intro _ _ _ _ _ _ h hm 
    exact lt_of_lt_of_leₓ (of_done h) (mono.of_done hm)

instance failure : @Parser.Prog α failure :=
  prog.of_step

theorem guard_true : ¬prog (guardₓ True) :=
  pure _

instance guardₓ : prog (guardₓ False) :=
  prog.failure

instance orelse [p.prog] [q.prog] : (p <|> q).Prog :=
  ⟨fun _ _ _ _ =>
      by 
        simpRw [orelse_eq_done]
        rintro (h | ⟨h, -⟩) <;> exact of_done h⟩

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem decorate_errors_iff : «expr ↔ »((@parser.decorate_errors α msgs p).prog, p.prog) :=
begin
  split,
  { introI [],
    constructor,
    intros [ident cb, ident n, ident n', ident a, ident h],
    have [] [":", expr «expr = »(@parser.decorate_errors α msgs p cb n, done n' a)] [":=", expr by simpa [] [] [] [] [] ["using", expr h]],
    exact [expr of_done this] },
  { introI [],
    constructor,
    intros ["_", "_", "_", "_", ident h],
    rw [expr decorate_errors_eq_done] ["at", ident h],
    exact [expr of_done h] }
end

instance decorate_errors [p.prog] : (@decorate_errors α msgs p).Prog :=
  ⟨fun _ _ _ _ =>
      by 
        rw [decorate_errors_eq_done]
        exact of_done⟩

theorem decorate_error_iff : (@Parser.decorateError α msg p).Prog ↔ p.prog :=
  decorate_errors_iff

instance decorate_error [p.prog] : (@decorate_error α msg p).Prog :=
  prog.decorate_errors

instance any_char : prog any_char :=
  prog.of_step

instance sat {p : Charₓ → Prop} [DecidablePred p] : prog (sat p) :=
  prog.of_step

theorem eps : ¬prog eps :=
  prog.pure ()

instance ch {c : Charₓ} : prog (ch c) :=
  prog.of_step

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem char_buf_iff {cb' : char_buffer} : «expr ↔ »((char_buf cb').prog, «expr ≠ »(cb', buffer.nil)) :=
begin
  have [] [":", expr «expr ↔ »(«expr ≠ »(cb', buffer.nil), «expr ≠ »(cb'.to_list, «expr[ , ]»([])))] [":=", expr not_iff_not_of_iff ⟨λ
    h, by simp [] [] [] ["[", expr h, "]"] [] [], λ
    h, by simpa [] [] [] [] [] ["using", expr congr_arg list.to_buffer h]⟩],
  rw ["[", expr char_buf, ",", expr this, ",", expr decorate_error_iff, "]"] [],
  cases [expr cb'.to_list] [],
  { simp [] [] [] ["[", expr pure, "]"] [] [] },
  { simp [] [] ["only"] ["[", expr iff_true, ",", expr ne.def, ",", expr not_false_iff, "]"] [] [],
    apply_instance }
end

instance one_of {cs : List Charₓ} : (one_of cs).Prog :=
  prog.decorate_errors

instance one_of' {cs : List Charₓ} : (one_of' cs).Prog :=
  prog.and_then

theorem str_iff {s : Stringₓ} : (str s).Prog ↔ s ≠ "" :=
  by 
    simp [str_eq_char_buf, char_buf_iff, ←Stringₓ.to_list_inj, Buffer.ext_iff]

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem remaining : «expr¬ »(remaining.prog) :=
begin
  introI [ident h],
  have [] [":", expr «expr = »(remaining buffer.nil 0, done 0 0)] [":=", expr by simp [] [] [] ["[", expr remaining_eq_done, "]"] [] []],
  replace [ident this] [":", expr «expr < »(0, 0)] [":=", expr prog.of_done this],
  exact [expr lt_irrefl _ this]
end

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eof : «expr¬ »(eof.prog) :=
begin
  introI [ident h],
  have [] [":", expr «expr = »(eof buffer.nil 0, done 0 ())] [":=", expr by simpa [] [] [] ["[", expr remaining_eq_done, "]"] [] []],
  replace [ident this] [":", expr «expr < »(0, 0)] [":=", expr prog.of_done this],
  exact [expr lt_irrefl _ this]
end

instance many1 [p.mono] [p.prog] : p.many1.prog :=
  by 
    constructor 
    rintro cb n n' (_ | ⟨hd, tl⟩)
    ·
      simp 
    ·
      rw [many1_eq_done]
      rintro ⟨np, hp, h⟩
      exact (of_done hp).trans_le (mono.of_done h)

theorem fix_core {F : Parser α → Parser α} (hF : ∀ (p : Parser α), p.prog → (F p).Prog) :
  ∀ (max_depth : ℕ), prog (fix_core F max_depth)
| 0 => prog.failure
| max_depth+1 => hF _ (fix_core _)

instance digit : digit.Prog :=
  prog.of_step

instance Nat : Nat.Prog :=
  prog.decorate_error

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fix {F : parser α → parser α} (hF : ∀ p : parser α, p.prog → (F p).prog) : prog (fix F) :=
⟨λ cb n _ _ h, by { haveI [] [] [":=", expr fix_core hF «expr + »(«expr - »(cb.size, n), 1)],
   dsimp [] ["[", expr fix, "]"] [] ["at", ident h],
   exact [expr of_done h] }⟩

end Prog

variable{α β : Type}{msgs : Thunkₓ (List Stringₓ)}{msg : Thunkₓ Stringₓ}

variable{p q : Parser α}{cb : CharBuffer}{n n' : ℕ}{err : Dlist Stringₓ}

variable{a : α}{b : β}

section Many

theorem many_sublist_of_done [p.step] [p.bounded] {l : List α} (h : p.many cb n = done n' l) :
  ∀ k (_ : k < n' - n), p.many cb (n+k) = done n' (l.drop k) :=
  by 
    induction' l with hd tl hl generalizing n
    ·
      rw [many_eq_done_nil] at h 
      simp [h.left]
    intro m hm 
    cases m
    ·
      exact h 
    rw [List.dropₓ, Nat.add_succ, ←Nat.succ_add]
    apply hl
    ·
      rw [←many1_eq_done_iff_many_eq_done, many1_eq_done] at h 
      obtain ⟨_, hp, h⟩ := h 
      convert h 
      exact (step.of_done hp).symm
    ·
      exact nat.lt_pred_iff.mpr hm

theorem many_eq_nil_of_done [p.step] [p.bounded] {l : List α} (h : p.many cb n = done n' l) :
  p.many cb n' = done n' [] :=
  by 
    induction' l with hd tl hl generalizing n
    ·
      convert h 
      rw [many_eq_done_nil] at h 
      exact h.left.symm
    ·
      rw [←many1_eq_done_iff_many_eq_done, many1_eq_done] at h 
      obtain ⟨_, -, h⟩ := h 
      exact hl h

theorem many_eq_nil_of_out_of_bound [p.bounded] {l : List α} (h : p.many cb n = done n' l) (hn : cb.size < n) :
  n' = n ∧ l = [] :=
  by 
    cases l
    ·
      rw [many_eq_done_nil] at h 
      exact ⟨h.left.symm, rfl⟩
    ·
      rw [many_eq_done] at h 
      obtain ⟨np, hp, -⟩ := h 
      exact absurd (bounded.of_done hp) hn.not_lt

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem many1_length_of_done
[p.mono]
[p.step]
[p.bounded]
{l : list α}
(h : «expr = »(many1 p cb n, done n' l)) : «expr = »(l.length, «expr - »(n', n)) :=
begin
  induction [expr l] [] ["with", ident hd, ident tl, ident hl] ["generalizing", ident n, ident n'],
  { simpa [] [] [] [] [] ["using", expr h] },
  { obtain ["⟨", ident k, ",", ident hk, "⟩", ":", expr «expr∃ , »((k), «expr = »(n', «expr + »(«expr + »(n, k), 1))), ":=", expr nat.exists_eq_add_of_lt (prog.of_done h)],
    subst [expr hk],
    simp [] [] ["only"] ["[", expr many1_eq_done, "]"] [] ["at", ident h],
    obtain ["⟨", "_", ",", ident hp, ",", ident h, "⟩", ":=", expr h],
    have [] [] [":=", expr step.of_done hp],
    subst [expr this],
    cases [expr tl] [],
    { simp [] [] ["only"] ["[", expr many_eq_done_nil, ",", expr add_left_inj, ",", expr exists_and_distrib_right, ",", expr self_eq_add_right, "]"] [] ["at", ident h],
      rcases [expr h, "with", "⟨", ident rfl, ",", "-", "⟩"],
      simp [] [] [] [] [] [] },
    rw ["<-", expr many1_eq_done_iff_many_eq_done] ["at", ident h],
    specialize [expr hl h],
    simp [] [] [] ["[", expr hl, ",", expr add_comm, ",", expr add_assoc, ",", expr nat.sub_succ, "]"] [] [] }
end

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem many1_bounded_of_done
[p.step]
[p.bounded]
{l : list α}
(h : «expr = »(many1 p cb n, done n' l)) : «expr ≤ »(n', cb.size) :=
begin
  induction [expr l] [] ["with", ident hd, ident tl, ident hl] ["generalizing", ident n, ident n'],
  { simpa [] [] [] [] [] ["using", expr h] },
  { simp [] [] ["only"] ["[", expr many1_eq_done, "]"] [] ["at", ident h],
    obtain ["⟨", ident np, ",", ident hp, ",", ident h, "⟩", ":=", expr h],
    have [] [] [":=", expr step.of_done hp],
    subst [expr this],
    cases [expr tl] [],
    { simp [] [] ["only"] ["[", expr many_eq_done_nil, ",", expr exists_and_distrib_right, "]"] [] ["at", ident h],
      simpa [] [] [] ["[", "<-", expr h.left, "]"] [] ["using", expr bounded.of_done hp] },
    { rw ["<-", expr many1_eq_done_iff_many_eq_done] ["at", ident h],
      exact [expr hl h] } }
end

end Many

section Nat

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The `val : ℕ` produced by a successful parse of a `cb : char_buffer` is the numerical value
represented by the string of decimal digits (possibly padded with 0s on the left)
starting from the parsing position `n` and ending at position `n'`. The number
of characters parsed in is necessarily `n' - n`.

This is one of the directions of `nat_eq_done`.
-/
theorem nat_of_done
{val : exprℕ()}
(h : «expr = »(nat cb n, done n' val)) : «expr = »(val, nat.of_digits 10 (((cb.to_list.drop n).take «expr - »(n', n)).reverse.map (λ
   c, «expr - »(c.to_nat, '0'.to_nat)))) :=
begin
  have [ident natm] [":", expr «expr = »(nat._match_1, λ
    (d : exprℕ())
    (p), ⟨«expr + »(p.1, «expr * »(d, p.2)), «expr * »(p.2, 10)⟩)] [],
  { ext1 [] [],
    ext1 [] ["⟨", "⟩"],
    refl },
  have [ident hpow] [":", expr ∀
   l, «expr = »((list.foldr (λ
      (digit : exprℕ())
      (x : «expr × »(exprℕ(), exprℕ())), («expr + »(x.fst, «expr * »(digit, x.snd)), «expr * »(x.snd, 10))) (0, 1) l).snd, «expr ^ »(10, l.length))] [],
  { intro [ident l],
    induction [expr l] [] ["with", ident hd, ident tl, ident hl] [],
    { simp [] [] [] [] [] [] },
    { simp [] [] [] ["[", expr hl, ",", expr pow_succ, ",", expr mul_comm, "]"] [] [] } },
  simp [] [] ["only"] ["[", expr nat, ",", expr pure_eq_done, ",", expr natm, ",", expr decorate_error_eq_done, ",", expr bind_eq_done, "]"] [] ["at", ident h],
  obtain ["⟨", ident n', ",", ident l, ",", ident hp, ",", ident rfl, ",", ident rfl, "⟩", ":=", expr h],
  induction [expr l] [] ["with", ident lhd, ident ltl, ident IH] ["generalizing", ident n, ident n', ident cb],
  { simpa [] [] [] [] [] ["using", expr hp] },
  cases [expr hx, ":", expr list.drop n (buffer.to_list cb)] ["with", ident chd, ident ctl],
  { have [] [":", expr «expr ≤ »(cb.size, n)] [":=", expr by simpa [] [] [] [] [] ["using", expr list.drop_eq_nil_iff_le.mp hx]],
    exact [expr absurd (bounded.of_done hp) this.not_lt] },
  have [ident chdh] [":", expr «expr = »(«expr - »(chd.to_nat, '0'.to_nat), lhd)] [],
  { simp [] [] ["only"] ["[", expr many1_eq_done, "]"] [] ["at", ident hp],
    obtain ["⟨", "_", ",", ident hp, ",", "-", "⟩", ":=", expr hp],
    have [] [] [":=", expr step.of_done hp],
    subst [expr this],
    simp [] [] ["only"] ["[", expr digit_eq_done, ",", expr buffer.read_eq_nth_le_to_list, ",", expr hx, ",", expr buffer.length_to_list, ",", expr true_and, ",", expr add_left_inj, ",", expr list.length, ",", expr list.nth_le, ",", expr eq_self_iff_true, ",", expr exists_and_distrib_left, ",", expr fin.coe_mk, "]"] [] ["at", ident hp],
    rcases [expr hp, "with", "⟨", "_", ",", ident hn, ",", ident rfl, ",", "_", ",", "_", "⟩"],
    have [ident hn'] [":", expr «expr < »(n, cb.to_list.length)] [":=", expr by simpa [] [] [] [] [] ["using", expr hn]],
    rw ["<-", expr list.cons_nth_le_drop_succ hn'] ["at", ident hx],
    simp [] [] ["only"] [] [] ["at", ident hx],
    simp [] [] [] ["[", expr hx, "]"] [] [] },
  obtain ["⟨", ident k, ",", ident hk, "⟩", ":", expr «expr∃ , »((k), «expr = »(n', «expr + »(«expr + »(n, k), 1))), ":=", expr nat.exists_eq_add_of_lt (prog.of_done hp)],
  have [ident hdm] [":", expr «expr ∨ »(«expr = »(ltl, «expr[ , ]»([])), «expr = »(digit.many1 cb «expr + »(n, 1), done n' ltl))] [],
  { cases [expr ltl] [],
    { simp [] [] [] [] [] [] },
    { rw [expr many1_eq_done] ["at", ident hp],
      obtain ["⟨", "_", ",", ident hp, ",", ident hp', "⟩", ":=", expr hp],
      simpa [] [] [] ["[", expr step.of_done hp, ",", expr many1_eq_done_iff_many_eq_done, "]"] [] ["using", expr hp'] } },
  rcases [expr hdm, "with", ident rfl, "|", ident hdm],
  { simp [] [] ["only"] ["[", expr many1_eq_done, ",", expr many_eq_done_nil, ",", expr exists_and_distrib_right, "]"] [] ["at", ident hp],
    obtain ["⟨", "_", ",", ident hp, ",", ident rfl, ",", ident hp', "⟩", ":=", expr hp],
    have [] [] [":=", expr step.of_done hp],
    subst [expr this],
    simp [] [] [] ["[", expr chdh, "]"] [] [] },
  have [ident rearr] [":", expr «expr = »(list.take «expr - »(«expr + »(n, «expr + »(k, 1)), «expr + »(n, 1)) (list.drop «expr + »(n, 1) (buffer.to_list cb)), ctl.take k)] [],
  { simp [] [] [] ["[", "<-", expr list.tail_drop, ",", expr hx, ",", expr nat.sub_succ, ",", expr hk, "]"] [] [] },
  have [ident ltll] [":", expr «expr = »(min k ctl.length, ltl.length)] [],
  { have [] [":", expr «expr = »((ctl.take k).length, min k ctl.length)] [":=", expr by simp [] [] [] [] [] []],
    rw ["[", "<-", expr this, ",", "<-", expr rearr, ",", expr many1_length_of_done hdm, "]"] [],
    have [] [":", expr «expr = »(k, «expr - »(«expr - »(n', n), 1))] [],
    { simp [] [] [] ["[", expr hk, ",", expr add_assoc, "]"] [] [] },
    subst [expr this],
    simp [] [] ["only"] ["[", expr nat.sub_succ, ",", expr add_comm, ",", "<-", expr nat.pred_sub, ",", expr buffer.length_to_list, ",", expr nat.pred_one_add, ",", expr min_eq_left_iff, ",", expr list.length_drop, ",", expr add_tsub_cancel_left, ",", expr list.length_take, ",", expr tsub_zero, "]"] [] [],
    rw ["[", expr tsub_le_tsub_iff_right, ",", expr nat.pred_le_iff, "]"] [],
    { convert [] [expr many1_bounded_of_done hp] [],
      cases [expr hc, ":", expr cb.size] [],
      { have [] [] [":=", expr bounded.of_done hp],
        rw [expr hc] ["at", ident this],
        exact [expr absurd n.zero_le this.not_le] },
      { simp [] [] [] [] [] [] } },
    { exact [expr nat.le_pred_of_lt (bounded.of_done hp)] } },
  simp [] [] [] ["[", expr IH _ hdm, ",", expr hx, ",", expr hk, ",", expr rearr, ",", "<-", expr chdh, ",", "<-", expr ltll, ",", expr hpow, ",", expr add_assoc, ",", expr nat.of_digits_append, ",", expr mul_comm, "]"] [] []
end

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If we know that `parser.nat` was successful, starting at position `n` and ending at position `n'`,
then it must be the case that for all `k : ℕ`, `n ≤ k`, `k < n'`, the character at the `k`th
position in `cb : char_buffer` is "numeric", that is, is between `'0'` and `'9'` inclusive.

This is a necessary part of proving one of the directions of `nat_eq_done`.
-/
theorem nat_of_done_as_digit
{val : exprℕ()}
(h : «expr = »(nat cb n, done n' val)) : ∀
(hn : «expr ≤ »(n', cb.size))
(k)
(hk : «expr < »(k, n')), «expr ≤ »(n, k) → «expr ∧ »(«expr ≤ »('0', cb.read ⟨k, hk.trans_le hn⟩), «expr ≤ »(cb.read ⟨k, hk.trans_le hn⟩, '9')) :=
begin
  simp [] [] ["only"] ["[", expr nat, ",", expr pure_eq_done, ",", expr and.left_comm, ",", expr decorate_error_eq_done, ",", expr bind_eq_done, ",", expr exists_eq_left, ",", expr exists_and_distrib_left, "]"] [] ["at", ident h],
  obtain ["⟨", ident xs, ",", ident h, ",", "-", "⟩", ":=", expr h],
  induction [expr xs] [] ["with", ident hd, ident tl, ident hl] ["generalizing", ident n, ident n'],
  { simpa [] [] [] [] [] ["using", expr h] },
  rw [expr many1_eq_done] ["at", ident h],
  obtain ["⟨", "_", ",", ident hp, ",", ident h, "⟩", ":=", expr h],
  simp [] [] ["only"] ["[", expr digit_eq_done, ",", expr and.comm, ",", expr and.left_comm, ",", expr digit_eq_fail, ",", expr true_and, ",", expr exists_eq_left, ",", expr eq_self_iff_true, ",", expr exists_and_distrib_left, ",", expr exists_and_distrib_left, "]"] [] ["at", ident hp],
  obtain ["⟨", ident rfl, ",", "-", ",", ident hn, ",", ident ge0, ",", ident le9, ",", ident rfl, "⟩", ":=", expr hp],
  intros [ident hn, ident k, ident hk, ident hk'],
  rcases [expr hk'.eq_or_lt, "with", ident rfl, "|", ident hk'],
  { exact [expr ⟨ge0, le9⟩] },
  cases [expr tl] [],
  { simp [] [] ["only"] ["[", expr many_eq_done_nil, ",", expr exists_and_distrib_right, "]"] [] ["at", ident h],
    obtain ["⟨", ident rfl, ",", "-", "⟩", ":=", expr h],
    have [] [":", expr «expr < »(k, k)] [":=", expr hk.trans_le (nat.succ_le_of_lt hk')],
    exact [expr absurd this (lt_irrefl _)] },
  { rw ["<-", expr many1_eq_done_iff_many_eq_done] ["at", ident h],
    apply [expr hl h],
    exact [expr nat.succ_le_of_lt hk'] }
end

/--
If we know that `parser.nat` was successful, starting at position `n` and ending at position `n'`,
then it must be the case that for the ending position `n'`, either it is beyond the end of the
`cb : char_buffer`, or the character at that position is not "numeric", that is,  between `'0'` and
`'9'` inclusive.

This is a necessary part of proving one of the directions of `nat_eq_done`.
-/
theorem nat_of_done_bounded {val : ℕ} (h : Nat cb n = done n' val) :
  ∀ (hn : n' < cb.size), '0' ≤ cb.read ⟨n', hn⟩ → '9' < cb.read ⟨n', hn⟩ :=
  by 
    simp only [Nat, pure_eq_done, And.left_comm, decorate_error_eq_done, bind_eq_done, exists_eq_left,
      exists_and_distrib_left] at h 
    obtain ⟨xs, h, -⟩ := h 
    induction' xs with hd tl hl generalizing n n'
    ·
      simpa using h 
    obtain ⟨k, hk⟩ : ∃ k, cb.size = (n+k)+1 := Nat.exists_eq_add_of_lt (bounded.of_done h)
    cases tl
    ·
      simp only [many1_eq_done, many_eq_done_nil, And.left_comm, exists_and_distrib_right, exists_eq_left] at h 
      obtain ⟨-, _, h⟩ := h 
      simp only [digit_eq_done, And.comm, And.left_comm, digit_eq_fail, true_andₓ, exists_eq_left, eq_self_iff_true,
        exists_and_distrib_left] at h 
      obtain ⟨rfl, h⟩ | ⟨h, -⟩ := h
      ·
        intro hn 
        simpa using h hn
      ·
        simpa using mono.of_fail h
    ·
      rw [many1_eq_done] at h 
      obtain ⟨_, -, h⟩ := h 
      rw [←many1_eq_done_iff_many_eq_done] at h 
      exact hl h

-- error in Data.Buffer.Parser.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The `val : ℕ` produced by a successful parse of a `cb : char_buffer` is the numerical value
represented by the string of decimal digits (possibly padded with 0s on the left)
starting from the parsing position `n` and ending at position `n'`, where `n < n'`. The number
of characters parsed in is necessarily `n' - n`. Additionally, all of the characters in the `cb`
starting at position `n` (inclusive) up to position `n'` (exclusive) are "numeric", in that they
are between `'0'` and `'9'` inclusive. Such a `char_buffer` would produce the `ℕ` value encoded
by its decimal characters.
-/
theorem nat_eq_done
{val : exprℕ()} : «expr ↔ »(«expr = »(nat cb n, done n' val), «expr∃ , »((hn : «expr < »(n, n')), «expr ∧ »(«expr = »(val, nat.of_digits 10 (((cb.to_list.drop n).take «expr - »(n', n)).reverse.map (λ
      c, «expr - »(c.to_nat, '0'.to_nat)))), «expr ∧ »(∀
    hn' : «expr < »(n', cb.size), «expr ≤ »('0', cb.read ⟨n', hn'⟩) → «expr < »('9', cb.read ⟨n', hn'⟩), «expr∃ , »((hn'' : «expr ≤ »(n', cb.size)), ∀
     (k)
     (hk : «expr < »(k, n')), «expr ≤ »(n, k) → «expr ∧ »(«expr ≤ »('0', cb.read ⟨k, hk.trans_le hn''⟩), «expr ≤ »(cb.read ⟨k, hk.trans_le hn''⟩, '9'))))))) :=
begin
  refine [expr ⟨λ h, ⟨prog.of_done h, nat_of_done h, nat_of_done_bounded h, _⟩, _⟩],
  { have [ident H] [] [":=", expr h],
    rw ["[", expr nat, "]"] ["at", ident h],
    simp [] [] ["only"] ["[", expr decorate_error_eq_done, ",", expr bind_eq_done, ",", expr pure_eq_done, ",", expr and.left_comm, ",", expr exists_eq_left, ",", expr exists_and_distrib_left, "]"] [] ["at", ident h],
    obtain ["⟨", "_", ",", ident h, ",", "-", "⟩", ":=", expr h],
    replace [ident h] [] [":=", expr many1_bounded_of_done h],
    exact [expr ⟨h, nat_of_done_as_digit H h⟩] },
  rintro ["⟨", ident hn, ",", ident hv, ",", ident hb, ",", ident hn', ",", ident ho, "⟩"],
  rw [expr nat] [],
  simp [] [] ["only"] ["[", expr and.left_comm, ",", expr pure_eq_done, ",", expr hv, ",", expr decorate_error_eq_done, ",", expr list.map_reverse, ",", expr bind_eq_done, ",", expr exists_eq_left, ",", expr exists_and_distrib_left, "]"] [] [],
  clear [ident hv, ident val],
  have [ident natm] [":", expr «expr = »(nat._match_1, λ
    (d : exprℕ())
    (p), ⟨«expr + »(p.1, «expr * »(d, p.2)), «expr * »(p.2, 10)⟩)] [],
  { ext1 [] [],
    ext1 [] ["⟨", "⟩"],
    refl },
  induction [expr H, ":", expr cb.to_list.drop n] [] ["with", ident hd, ident tl, ident IH] ["generalizing", ident n],
  { rw [expr list.drop_eq_nil_iff_le] ["at", ident H],
    refine [expr absurd ((lt_of_le_of_lt H hn).trans_le hn') _],
    simp [] [] [] [] [] [] },
  { specialize [expr @IH «expr + »(n, 1)],
    simp [] [] ["only"] ["[", "<-", expr list.cons_nth_le_drop_succ (show «expr < »(n, cb.to_list.length), by simpa [] [] [] [] [] ["using", expr hn.trans_le hn']), "]"] [] ["at", ident H],
    have [ident hdigit] [":", expr «expr = »(digit cb n, done «expr + »(n, 1) «expr - »(hd.to_nat, '0'.to_nat))] [],
    { specialize [expr ho n hn (le_refl _)],
      have [] [":", expr «expr ≤ »(«expr - »((buffer.read cb ⟨n, hn.trans_le hn'⟩).to_nat, '0'.to_nat), 9)] [],
      { rw ["[", expr show «expr = »(9, «expr - »('9'.to_nat, '0'.to_nat)), from exprdec_trivial(), ",", expr tsub_le_tsub_iff_right, "]"] [],
        { exact [expr ho.right] },
        { dec_trivial [] } },
      simp [] [] [] ["[", expr digit_eq_done, ",", expr this, ",", "<-", expr H.left, ",", expr buffer.nth_le_to_list, ",", expr hn.trans_le hn', ",", expr ho, "]"] [] [] },
    cases [expr lt_or_ge «expr + »(n, 1) n'] ["with", ident hn'', ident hn''],
    { specialize [expr IH hn'' _ H.right],
      { intros [ident k, ident hk, ident hk'],
        apply [expr ho],
        exact [expr nat.le_of_succ_le hk'] },
      obtain ["⟨", ident l, ",", ident hdl, ",", ident hvl, "⟩", ":=", expr IH],
      use [expr [«expr :: »/«expr :: »/«expr :: »](«expr - »(hd.to_nat, '0'.to_nat), l)],
      cases [expr l] ["with", ident lhd, ident ltl],
      { simpa [] [] [] [] [] ["using", expr hdl] },
      simp [] [] ["only"] ["[", expr natm, ",", expr list.foldr, "]"] [] ["at", ident hvl],
      simp [] [] ["only"] ["[", expr natm, ",", expr hvl, ",", expr many1_eq_done, ",", expr hdigit, ",", expr many1_eq_done_iff_many_eq_done.mp hdl, ",", expr true_and, ",", expr and_true, ",", expr eq_self_iff_true, ",", expr list.foldr, ",", expr exists_eq_left', "]"] [] [],
      obtain ["⟨", ident m, ",", ident rfl, "⟩", ":", expr «expr∃ , »((m), «expr = »(n', «expr + »(«expr + »(n, m), 1))), ":=", expr nat.exists_eq_add_of_lt hn],
      have [] [":", expr «expr = »(«expr - »(«expr + »(«expr + »(n, m), 1), n), «expr + »(m, 1))] [],
      { rw ["[", expr add_assoc, ",", expr tsub_eq_iff_eq_add_of_le, ",", expr add_comm, "]"] [],
        exact [expr nat.le_add_right _ _] },
      have [ident hpow] [":", expr ∀
       l, «expr = »((list.foldr (λ
          (digit : exprℕ())
          (x : «expr × »(exprℕ(), exprℕ())), («expr + »(x.fst, «expr * »(digit, x.snd)), «expr * »(x.snd, 10))) (0, 1) l).snd, «expr ^ »(10, l.length))] [],
      { intro [ident l],
        induction [expr l] [] ["with", ident hd, ident tl, ident hl] [],
        { simp [] [] [] [] [] [] },
        { simp [] [] [] ["[", expr hl, ",", expr pow_succ, ",", expr mul_comm, "]"] [] [] } },
      have [ident hml] [":", expr «expr = »(«expr + »(ltl.length, 1), m)] [":=", expr by simpa [] [] [] [] [] ["using", expr many1_length_of_done hdl]],
      have [ident ltll] [":", expr «expr = »(min m tl.length, m)] [],
      { simpa [] [] [] ["[", "<-", expr H.right, ",", expr le_tsub_iff_right (hn''.trans_le hn').le, ",", expr add_comm, ",", expr add_assoc, ",", expr add_left_comm, "]"] [] ["using", expr hn'] },
      simp [] [] [] ["[", expr this, ",", expr hpow, ",", expr nat.of_digits_append, ",", expr mul_comm, ",", "<-", expr pow_succ 10, ",", expr hml, ",", expr ltll, "]"] [] [] },
    { have [] [":", expr «expr = »(n', «expr + »(n, 1))] [":=", expr le_antisymm hn'' (nat.succ_le_of_lt hn)],
      subst [expr this],
      use ["[", expr «expr[ , ]»([«expr - »(hd.to_nat, '0'.to_nat)]), "]"],
      simp [] [] ["only"] ["[", expr many1_eq_done, ",", expr many_eq_done_nil, ",", expr digit_eq_fail, ",", expr natm, ",", expr and.comm, ",", expr and.left_comm, ",", expr hdigit, ",", expr true_and, ",", expr mul_one, ",", expr nat.of_digits_singleton, ",", expr list.take, ",", expr exists_eq_left, ",", expr exists_and_distrib_right, ",", expr add_tsub_cancel_left, ",", expr eq_self_iff_true, ",", expr list.reverse_singleton, ",", expr zero_add, ",", expr list.foldr, ",", expr list.map, "]"] [] [],
      refine [expr ⟨_, or.inl ⟨rfl, _⟩⟩],
      simpa [] [] [] [] [] ["using", expr hb] } }
end

end Nat

end Parser

