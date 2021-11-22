import Mathbin.Control.Monad.Writer

universe u v w u₀ u₁ v₀ v₁

structure MonadCont.Label(α : Type w)(m : Type u → Type v)(β : Type u) where 
  apply : α → m β

def MonadCont.goto {α β} {m : Type u → Type v} (f : MonadCont.Label α m β) (x : α) :=
  f.apply x

class MonadCont(m : Type u → Type v) where 
  callCc : ∀ {α β}, (MonadCont.Label α m β → m α) → m α

open MonadCont

class IsLawfulMonadCont(m : Type u → Type v)[Monadₓ m][MonadCont m] extends IsLawfulMonad m where 
  call_cc_bind_right {α ω γ} (cmd : m α) (next : label ω m γ → α → m ω) :
  (call_cc fun f => cmd >>= next f) = cmd >>= fun x => call_cc fun f => next f x 
  call_cc_bind_left {α} β (x : α) (dead : label α m β → β → m α) :
  (call_cc fun f : label α m β => goto f x >>= dead f) = pure x 
  call_cc_dummy {α β} (dummy : m α) : (call_cc fun f : label α m β => dummy) = dummy

export IsLawfulMonadCont()

def ContT (r : Type u) (m : Type u → Type v) (α : Type w) :=
  (α → m r) → m r

@[reducible]
def Cont (r : Type u) (α : Type w) :=
  ContT r id α

namespace ContT

export MonadCont(Label goto)

variable{r : Type u}{m : Type u → Type v}{α β γ ω : Type w}

def run : ContT r m α → (α → m r) → m r :=
  id

def map (f : m r → m r) (x : ContT r m α) : ContT r m α :=
  f ∘ x

theorem run_cont_t_map_cont_t (f : m r → m r) (x : ContT r m α) : run (map f x) = f ∘ run x :=
  rfl

def with_cont_t (f : (β → m r) → α → m r) (x : ContT r m α) : ContT r m β :=
  fun g => x$ f g

theorem run_with_cont_t (f : (β → m r) → α → m r) (x : ContT r m α) : run (with_cont_t f x) = run x ∘ f :=
  rfl

@[ext]
protected theorem ext {x y : ContT r m α} (h : ∀ f, x.run f = y.run f) : x = y :=
  by 
    ext <;> apply h

instance  : Monadₓ (ContT r m) :=
  { pure := fun α x f => f x, bind := fun α β x f g => x$ fun i => f i g }

instance  : IsLawfulMonad (ContT r m) :=
  { id_map :=
      by 
        intros 
        rfl,
    pure_bind :=
      by 
        intros 
        ext 
        rfl,
    bind_assoc :=
      by 
        intros 
        ext 
        rfl }

def monad_lift [Monadₓ m] {α} : m α → ContT r m α :=
  fun x f => x >>= f

instance  [Monadₓ m] : HasMonadLift m (ContT r m) :=
  { monadLift := fun α => ContT.monadLift }

theorem monad_lift_bind [Monadₓ m] [IsLawfulMonad m] {α β} (x : m α) (f : α → m β) :
  (monad_lift (x >>= f) : ContT r m β) = monad_lift x >>= monad_lift ∘ f :=
  by 
    ext 
    simp only [monad_lift, HasMonadLift.monadLift, · ∘ ·, · >>= ·, bind_assoc, id.def, run, ContT.monadLift]

instance  : MonadCont (ContT r m) :=
  { callCc := fun α β f g => f ⟨fun x h => g x⟩ g }

instance  : IsLawfulMonadCont (ContT r m) :=
  { call_cc_bind_right :=
      by 
        intros  <;> ext <;> rfl,
    call_cc_bind_left :=
      by 
        intros  <;> ext <;> rfl,
    call_cc_dummy :=
      by 
        intros  <;> ext <;> rfl }

instance  ε [MonadExcept ε m] : MonadExcept ε (ContT r m) :=
  { throw := fun x e f => throw e, catch := fun α act h f => catch (act f) fun e => h e f }

instance  : MonadRun (fun α => (α → m r) → Ulift.{u, v} (m r)) (ContT.{u, v, u} r m) :=
  { run := fun α f x => ⟨f x⟩ }

end ContT

variable{m : Type u → Type v}[Monadₓ m]

def ExceptTₓ.mkLabel {α β ε} : label (Except.{u, u} ε α) m β → label α (ExceptTₓ ε m) β
| ⟨f⟩ => ⟨fun a => monad_lift$ f (Except.ok a)⟩

theorem ExceptTₓ.goto_mk_label {α β ε : Type _} (x : label (Except.{u, u} ε α) m β) (i : α) :
  goto (ExceptTₓ.mkLabel x) i = ⟨Except.ok <$> goto x (Except.ok i)⟩ :=
  by 
    cases x <;> rfl

def ExceptTₓ.callCc {ε} [MonadCont m] {α β : Type _} (f : label α (ExceptTₓ ε m) β → ExceptTₓ ε m α) : ExceptTₓ ε m α :=
  ExceptTₓ.mk (call_cc$ fun x : label _ m β => ExceptTₓ.run$ f (ExceptTₓ.mkLabel x) : m (Except ε α))

instance  {ε} [MonadCont m] : MonadCont (ExceptTₓ ε m) :=
  { callCc := fun α β => ExceptTₓ.callCc }

instance  {ε} [MonadCont m] [IsLawfulMonadCont m] : IsLawfulMonadCont (ExceptTₓ ε m) :=
  { call_cc_bind_right :=
      by 
        intros 
        simp [call_cc, ExceptTₓ.callCc, call_cc_bind_right]
        ext 
        dsimp 
        congr with ⟨⟩ <;> simp [ExceptTₓ.bindCont, @call_cc_dummy m _],
    call_cc_bind_left :=
      by 
        intros 
        simp [call_cc, ExceptTₓ.callCc, call_cc_bind_right, ExceptTₓ.goto_mk_label, map_eq_bind_pure_comp, bind_assoc,
          @call_cc_bind_left m _]
        ext 
        rfl,
    call_cc_dummy :=
      by 
        intros 
        simp [call_cc, ExceptTₓ.callCc, @call_cc_dummy m _]
        ext 
        rfl }

def OptionTₓ.mkLabel {α β} : label (Option.{u} α) m β → label α (OptionTₓ m) β
| ⟨f⟩ => ⟨fun a => monad_lift$ f (some a)⟩

theorem OptionTₓ.goto_mk_label {α β : Type _} (x : label (Option.{u} α) m β) (i : α) :
  goto (OptionTₓ.mkLabel x) i = ⟨some <$> goto x (some i)⟩ :=
  by 
    cases x <;> rfl

def OptionTₓ.callCc [MonadCont m] {α β : Type _} (f : label α (OptionTₓ m) β → OptionTₓ m α) : OptionTₓ m α :=
  OptionTₓ.mk (call_cc$ fun x : label _ m β => OptionTₓ.run$ f (OptionTₓ.mkLabel x) : m (Option α))

instance  [MonadCont m] : MonadCont (OptionTₓ m) :=
  { callCc := fun α β => OptionTₓ.callCc }

instance  [MonadCont m] [IsLawfulMonadCont m] : IsLawfulMonadCont (OptionTₓ m) :=
  { call_cc_bind_right :=
      by 
        intros 
        simp [call_cc, OptionTₓ.callCc, call_cc_bind_right]
        ext 
        dsimp 
        congr with ⟨⟩ <;> simp [OptionTₓ.bindCont, @call_cc_dummy m _],
    call_cc_bind_left :=
      by 
        intros 
        simp [call_cc, OptionTₓ.callCc, call_cc_bind_right, OptionTₓ.goto_mk_label, map_eq_bind_pure_comp, bind_assoc,
          @call_cc_bind_left m _]
        ext 
        rfl,
    call_cc_dummy :=
      by 
        intros 
        simp [call_cc, OptionTₓ.callCc, @call_cc_dummy m _]
        ext 
        rfl }

def WriterT.mkLabelₓ {α β ω} [HasOne ω] : label (α × ω) m β → label α (WriterT ω m) β
| ⟨f⟩ => ⟨fun a => monad_lift$ f (a, 1)⟩

theorem WriterT.goto_mk_label {α β ω : Type _} [HasOne ω] (x : label (α × ω) m β) (i : α) :
  goto (WriterT.mkLabelₓ x) i = monad_lift (goto x (i, 1)) :=
  by 
    cases x <;> rfl

def WriterT.callCc [MonadCont m] {α β ω : Type _} [HasOne ω] (f : label α (WriterT ω m) β → WriterT ω m α) :
  WriterT ω m α :=
  ⟨call_cc (WriterT.run ∘ f ∘ WriterT.mkLabelₓ : label (α × ω) m β → m (α × ω))⟩

instance  ω [Monadₓ m] [HasOne ω] [MonadCont m] : MonadCont (WriterT ω m) :=
  { callCc := fun α β => WriterT.callCc }

def StateTₓ.mkLabelₓ {α β σ : Type u} : label (α × σ) m (β × σ) → label α (StateTₓ σ m) β
| ⟨f⟩ => ⟨fun a => ⟨fun s => f (a, s)⟩⟩

theorem StateTₓ.goto_mk_label {α β σ : Type u} (x : label (α × σ) m (β × σ)) (i : α) :
  goto (StateTₓ.mkLabelₓ x) i = ⟨fun s => goto x (i, s)⟩ :=
  by 
    cases x <;> rfl

def StateTₓ.callCc {σ} [MonadCont m] {α β : Type _} (f : label α (StateTₓ σ m) β → StateTₓ σ m α) : StateTₓ σ m α :=
  ⟨fun r => call_cc fun f' => (f$ StateTₓ.mkLabelₓ f').run r⟩

instance  {σ} [MonadCont m] : MonadCont (StateTₓ σ m) :=
  { callCc := fun α β => StateTₓ.callCc }

instance  {σ} [MonadCont m] [IsLawfulMonadCont m] : IsLawfulMonadCont (StateTₓ σ m) :=
  { call_cc_bind_right :=
      by 
        intros 
        simp [call_cc, StateTₓ.callCc, call_cc_bind_right, · >>= ·, StateTₓ.bind]
        ext 
        dsimp 
        congr with ⟨x₀, x₁⟩
        rfl,
    call_cc_bind_left :=
      by 
        intros 
        simp [call_cc, StateTₓ.callCc, call_cc_bind_left, · >>= ·, StateTₓ.bind, StateTₓ.goto_mk_label]
        ext 
        rfl,
    call_cc_dummy :=
      by 
        intros 
        simp [call_cc, StateTₓ.callCc, call_cc_bind_right, · >>= ·, StateTₓ.bind, @call_cc_dummy m _]
        ext 
        rfl }

def ReaderTₓ.mkLabelₓ {α β} ρ : label α m β → label α (ReaderTₓ ρ m) β
| ⟨f⟩ => ⟨monad_lift ∘ f⟩

theorem ReaderTₓ.goto_mk_label {α ρ β} (x : label α m β) (i : α) :
  goto (ReaderTₓ.mkLabelₓ ρ x) i = monad_lift (goto x i) :=
  by 
    cases x <;> rfl

def ReaderTₓ.callCc {ε} [MonadCont m] {α β : Type _} (f : label α (ReaderTₓ ε m) β → ReaderTₓ ε m α) : ReaderTₓ ε m α :=
  ⟨fun r => call_cc fun f' => (f$ ReaderTₓ.mkLabelₓ _ f').run r⟩

instance  {ρ} [MonadCont m] : MonadCont (ReaderTₓ ρ m) :=
  { callCc := fun α β => ReaderTₓ.callCc }

instance  {ρ} [MonadCont m] [IsLawfulMonadCont m] : IsLawfulMonadCont (ReaderTₓ ρ m) :=
  { call_cc_bind_right :=
      by 
        intros 
        simp [call_cc, ReaderTₓ.callCc, call_cc_bind_right]
        ext 
        rfl,
    call_cc_bind_left :=
      by 
        intros 
        simp [call_cc, ReaderTₓ.callCc, call_cc_bind_left, ReaderTₓ.goto_mk_label]
        ext 
        rfl,
    call_cc_dummy :=
      by 
        intros 
        simp [call_cc, ReaderTₓ.callCc, @call_cc_dummy m _]
        ext 
        rfl }

/-- reduce the equivalence between two continuation passing monads to the equivalence between
their underlying monad -/
def ContT.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁} {α₁ r₁ : Type u₀} {α₂ r₂ : Type u₁}
  (F : m₁ r₁ ≃ m₂ r₂) (G : α₁ ≃ α₂) : ContT r₁ m₁ α₁ ≃ ContT r₂ m₂ α₂ :=
  { toFun := fun f r => F$ f$ fun x => F.symm$ r$ G x, invFun := fun f r => F.symm$ f$ fun x => F$ r$ G.symm x,
    left_inv :=
      fun f =>
        by 
          funext r <;> simp ,
    right_inv :=
      fun f =>
        by 
          funext r <;> simp  }

