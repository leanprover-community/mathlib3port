import Mathbin.Topology.Bases 
import Mathbin.Data.Analysis.Filter

open Set

open Filter hiding Realizer

open_locale TopologicalSpace

/-- A `ctop α σ` is a realization of a topology (basis) on `α`,
  represented by a type `σ` together with operations for the top element and
  the intersection operation. -/
structure Ctop(α σ : Type _) where 
  f : σ → Set α 
  top : α → σ 
  top_mem : ∀ (x : α), x ∈ f (top x)
  inter : ∀ a b (x : α), x ∈ f a ∩ f b → σ 
  inter_mem : ∀ a b x h, x ∈ f (inter a b x h)
  inter_sub : ∀ a b x h, f (inter a b x h) ⊆ f a ∩ f b

variable{α : Type _}{β : Type _}{σ : Type _}{τ : Type _}

namespace Ctop

section 

variable(F : Ctop α σ)

instance  : CoeFun (Ctop α σ) fun _ => σ → Set α :=
  ⟨Ctop.F⟩

@[simp]
theorem coe_mk f T h₁ I h₂ h₃ a : (@Ctop.mk α σ f T h₁ I h₂ h₃) a = f a :=
  rfl

/-- Map a ctop to an equivalent representation type. -/
def of_equiv (E : σ ≃ τ) : Ctop α σ → Ctop α τ
| ⟨f, T, h₁, I, h₂, h₃⟩ =>
  { f := fun a => f (E.symm a), top := fun x => E (T x),
    top_mem :=
      fun x =>
        by 
          simpa using h₁ x,
    inter := fun a b x h => E (I (E.symm a) (E.symm b) x h),
    inter_mem :=
      fun a b x h =>
        by 
          simpa using h₂ (E.symm a) (E.symm b) x h,
    inter_sub :=
      fun a b x h =>
        by 
          simpa using h₃ (E.symm a) (E.symm b) x h }

@[simp]
theorem of_equiv_val (E : σ ≃ τ) (F : Ctop α σ) (a : τ) : F.of_equiv E a = F (E.symm a) :=
  by 
    cases F <;> rfl

end 

/-- Every `ctop` is a topological space. -/
def to_topsp (F : Ctop α σ) : TopologicalSpace α :=
  TopologicalSpace.generateFrom (Set.Range F.f)

-- error in Data.Analysis.Topology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem to_topsp_is_topological_basis
(F : ctop α σ) : @topological_space.is_topological_basis _ F.to_topsp (set.range F.f) :=
by letI [] [] [":=", expr F.to_topsp]; exact [expr ⟨λ
  (u)
  ⟨a, e₁⟩
  (v)
  ⟨b, e₂⟩, «expr ▸ »(e₁, «expr ▸ »(e₂, λ
    x
    h, ⟨_, ⟨_, rfl⟩, F.inter_mem a b x h, F.inter_sub a b x h⟩)), «expr $ »(eq_univ_iff_forall.2, λ
   x, ⟨_, ⟨_, rfl⟩, F.top_mem x⟩), rfl⟩]

@[simp]
theorem mem_nhds_to_topsp (F : Ctop α σ) {s : Set α} {a : α} : s ∈ @nhds _ F.to_topsp a ↔ ∃ b, a ∈ F b ∧ F b ⊆ s :=
  (@TopologicalSpace.IsTopologicalBasis.mem_nhds_iff _ F.to_topsp _ _ _ F.to_topsp_is_topological_basis).trans$
    ⟨fun ⟨_, ⟨x, rfl⟩, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨_, ⟨x, rfl⟩, h⟩⟩

end Ctop

/-- A `ctop` realizer for the topological space `T` is a `ctop`
  which generates `T`. -/
structure Ctop.Realizer(α)[T : TopologicalSpace α] where 
  σ : Type _ 
  f : Ctop α σ 
  Eq : F.to_topsp = T

open Ctop

protected def Ctop.toRealizer (F : Ctop α σ) : @Ctop.Realizer _ F.to_topsp :=
  @Ctop.Realizer.mk _ F.to_topsp σ F rfl

namespace Ctop.Realizer

-- error in Data.Analysis.Topology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem is_basis
[T : topological_space α]
(F : realizer α) : topological_space.is_topological_basis (set.range F.F.f) :=
by have [] [] [":=", expr to_topsp_is_topological_basis F.F]; rwa [expr F.eq] ["at", ident this]

-- error in Data.Analysis.Topology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem mem_nhds
[T : topological_space α]
(F : realizer α)
{s : set α}
{a : α} : «expr ↔ »(«expr ∈ »(s, expr𝓝() a), «expr∃ , »((b), «expr ∧ »(«expr ∈ »(a, F.F b), «expr ⊆ »(F.F b, s)))) :=
by have [] [] [":=", expr mem_nhds_to_topsp F.F]; rwa [expr F.eq] ["at", ident this]

theorem is_open_iff [TopologicalSpace α] (F : realizer α) {s : Set α} :
  IsOpen s ↔ ∀ a (_ : a ∈ s), ∃ b, a ∈ F.F b ∧ F.F b ⊆ s :=
  is_open_iff_mem_nhds.trans$ ball_congr$ fun a h => F.mem_nhds

-- error in Data.Analysis.Topology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_closed_iff
[topological_space α]
(F : realizer α)
{s : set α} : «expr ↔ »(is_closed s, ∀
 a, ∀ b, «expr ∈ »(a, F.F b) → «expr∃ , »((z), «expr ∈ »(z, «expr ∩ »(F.F b, s))) → «expr ∈ »(a, s)) :=
«expr $ »(is_open_compl_iff.symm.trans, «expr $ »(F.is_open_iff.trans, «expr $ »(forall_congr, λ
   a, show «expr ↔ »(«expr ∉ »(a, s) → «expr∃ , »((b : F.σ), «expr ∧ »(«expr ∈ »(a, F.F b), ∀
      z «expr ∈ » F.F b, «expr ∉ »(z, s))), _), by haveI [] [] [":=", expr classical.prop_decidable]; rw ["[", expr not_imp_comm, "]"] []; simp [] [] [] ["[", expr not_exists, ",", expr not_and, ",", expr not_forall, ",", expr and_comm, "]"] [] [])))

theorem mem_interior_iff [TopologicalSpace α] (F : realizer α) {s : Set α} {a : α} :
  a ∈ Interior s ↔ ∃ b, a ∈ F.F b ∧ F.F b ⊆ s :=
  mem_interior_iff_mem_nhds.trans F.mem_nhds

protected theorem IsOpen [TopologicalSpace α] (F : realizer α) (s : F.σ) : IsOpen (F.F s) :=
  is_open_iff_nhds.2$
    fun a m =>
      by 
        simpa using F.mem_nhds.2 ⟨s, m, subset.refl _⟩

theorem ext' [T : TopologicalSpace α] {σ : Type _} {F : Ctop α σ} (H : ∀ a s, s ∈ 𝓝 a ↔ ∃ b, a ∈ F b ∧ F b ⊆ s) :
  F.to_topsp = T :=
  by 
    refine' eq_of_nhds_eq_nhds fun x => _ 
    ext s 
    rw [mem_nhds_to_topsp, H]

theorem ext [T : TopologicalSpace α] {σ : Type _} {F : Ctop α σ} (H₁ : ∀ a, IsOpen (F a))
  (H₂ : ∀ a s, s ∈ 𝓝 a → ∃ b, a ∈ F b ∧ F b ⊆ s) : F.to_topsp = T :=
  ext'$ fun a s => ⟨H₂ a s, fun ⟨b, h₁, h₂⟩ => mem_nhds_iff.2 ⟨_, h₂, H₁ _, h₁⟩⟩

variable[TopologicalSpace α]

protected def id : realizer α :=
  ⟨{ x : Set α // IsOpen x },
    { f := Subtype.val, top := fun _ => ⟨univ, is_open_univ⟩, top_mem := mem_univ,
      inter := fun ⟨x, h₁⟩ ⟨y, h₂⟩ a h₃ => ⟨_, h₁.inter h₂⟩, inter_mem := fun ⟨x, h₁⟩ ⟨y, h₂⟩ a => id,
      inter_sub := fun ⟨x, h₁⟩ ⟨y, h₂⟩ a h₃ => subset.refl _ },
    ext Subtype.property$
      fun x s h =>
        let ⟨t, h, o, m⟩ := mem_nhds_iff.1 h
        ⟨⟨t, o⟩, m, h⟩⟩

def of_equiv (F : realizer α) (E : F.σ ≃ τ) : realizer α :=
  ⟨τ, F.F.of_equiv E,
    ext'
      fun a s =>
        F.mem_nhds.trans$
          ⟨fun ⟨s, h⟩ =>
              ⟨E s,
                by 
                  simpa using h⟩,
            fun ⟨t, h⟩ =>
              ⟨E.symm t,
                by 
                  simpa using h⟩⟩⟩

@[simp]
theorem of_equiv_σ (F : realizer α) (E : F.σ ≃ τ) : (F.of_equiv E).σ = τ :=
  rfl

@[simp]
theorem of_equiv_F (F : realizer α) (E : F.σ ≃ τ) (s : τ) : (F.of_equiv E).f s = F.F (E.symm s) :=
  by 
    delta' of_equiv <;> simp 

protected def nhds (F : realizer α) (a : α) : (𝓝 a).Realizer :=
  ⟨{ s : F.σ // a ∈ F.F s },
    { f := fun s => F.F s.1, pt := ⟨_, F.F.top_mem a⟩, inf := fun ⟨x, h₁⟩ ⟨y, h₂⟩ => ⟨_, F.F.inter_mem x y a ⟨h₁, h₂⟩⟩,
      inf_le_left := fun ⟨x, h₁⟩ ⟨y, h₂⟩ z h => (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).1,
      inf_le_right := fun ⟨x, h₁⟩ ⟨y, h₂⟩ z h => (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).2 },
    filter_eq$
      Set.ext$
        fun x =>
          ⟨fun ⟨⟨s, as⟩, h⟩ => mem_nhds_iff.2 ⟨_, h, F.is_open _, as⟩,
            fun h =>
              let ⟨s, h, as⟩ := F.mem_nhds.1 h
              ⟨⟨s, h⟩, as⟩⟩⟩

@[simp]
theorem nhds_σ (m : α → β) (F : realizer α) (a : α) : (F.nhds a).σ = { s : F.σ // a ∈ F.F s } :=
  rfl

@[simp]
theorem nhds_F (m : α → β) (F : realizer α) (a : α) s : (F.nhds a).f s = F.F s.1 :=
  rfl

theorem tendsto_nhds_iff {m : β → α} {f : Filter β} (F : f.realizer) (R : realizer α) {a : α} :
  tendsto m f (𝓝 a) ↔ ∀ t, a ∈ R.F t → ∃ s, ∀ x (_ : x ∈ F.F s), m x ∈ R.F t :=
  (F.tendsto_iff _ (R.nhds a)).trans Subtype.forall

end Ctop.Realizer

structure LocallyFinite.Realizer[TopologicalSpace α](F : realizer α)(f : β → Set α) where 
  bas : ∀ a, { s // a ∈ F.F s }
  Sets : ∀ (x : α), Fintype { i | (f i ∩ F.F (bas x)).Nonempty }

theorem LocallyFinite.Realizer.to_locally_finite [TopologicalSpace α] {F : realizer α} {f : β → Set α}
  (R : LocallyFinite.Realizer F f) : LocallyFinite f :=
  fun a => ⟨_, F.mem_nhds.2 ⟨(R.bas a).1, (R.bas a).2, subset.refl _⟩, ⟨R.sets a⟩⟩

theorem locally_finite_iff_exists_realizer [TopologicalSpace α] (F : realizer α) {f : β → Set α} :
  LocallyFinite f ↔ Nonempty (LocallyFinite.Realizer F f) :=
  ⟨fun h =>
      let ⟨g, h₁⟩ := Classical.axiom_of_choice h 
      let ⟨g₂, h₂⟩ :=
        Classical.axiom_of_choice
          fun x =>
            show ∃ b : F.σ, x ∈ F.F b ∧ F.F b ⊆ g x from
              let ⟨h, h'⟩ := h₁ x 
              F.mem_nhds.1 h
      ⟨⟨fun x => ⟨g₂ x, (h₂ x).1⟩,
          fun x =>
            finite.fintype$
              let ⟨h, h'⟩ := h₁ x 
              h'.subset$ fun i hi => hi.mono (inter_subset_inter_right _ (h₂ x).2)⟩⟩,
    fun ⟨R⟩ => R.to_locally_finite⟩

def Compact.Realizer [TopologicalSpace α] (R : realizer α) (s : Set α) :=
  ∀ {f : Filter α} (F : f.realizer) (x : F.σ), f ≠ ⊥ → F.F x ⊆ s → { a // a ∈ s ∧ 𝓝 a⊓f ≠ ⊥ }

