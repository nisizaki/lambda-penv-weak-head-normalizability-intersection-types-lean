import LambdaPEnvWH.Syntax

/-!
# Intersection types with `ω` and environment types

Port of `Typing.thy`.

`Env m ob`: `m` is an association list (first binding wins), `ob = true` is the open tail
(essential), `ob = false` is the top tail (`Env [] false` plays the role of `ω` as an
environment).

Adaptations: Isabelle's `ty`, `sub`, `hasty` are `Ty`, `Sub`, `Hasty`; `map_of` is a Lean
function on association lists (first binding wins); `ob : bool` is `Bool` (a `Bool` `b`
is read as the proposition `b = true`).  Notation: `A ≼ B` for `Sub A B`
and `C ⊢ M : A` for `Hasty C M A`.
-/

namespace LambdaPEnvWH

open Trm

inductive Ty where
  | TV (n : Nat)
  | Om
  | Arr (A B : Ty)
  | Inter (A B : Ty)
  | Env (m : List (Var × Ty)) (ob : Bool)
  /-- name type `Q x`: the type of the quoted name `⌜x⌝` -/
  | QN (x : Var)

open Ty

/-- Association-list lookup; the first binding wins (Isabelle `map_of`). -/
def map_of : List (Var × Ty) → Var → Option Ty
  | [], _ => none
  | (y, A) :: m, x => if y = x then some A else map_of m x

def emeet (m1 m2 : List (Var × Ty)) : List (Var × Ty) :=
  m1.map (fun p => (p.1, match map_of m2 p.1 with | some B => Inter p.2 B | none => p.2)) ++ m2

theorem map_of_map_dep (f : Var → Ty → Ty) (m : List (Var × Ty)) (y : Var) :
    map_of (m.map (fun p => (p.1, f p.1 p.2))) y = (map_of m y).map (f y) := by
  induction m with
  | nil => simp [map_of]
  | cons p m ih =>
    obtain ⟨z, A⟩ := p
    by_cases h : z = y
    · subst h; simp [map_of]
    · simp [map_of, h, ih]

theorem map_of_append (m1 m2 : List (Var × Ty)) (y : Var) :
    map_of (m1 ++ m2) y = (match map_of m1 y with | some A => some A | none => map_of m2 y) := by
  induction m1 with
  | nil => simp [map_of]
  | cons p m ih =>
    obtain ⟨z, A⟩ := p
    by_cases h : z = y
    · subst h; simp [map_of]
    · simp [map_of, h, ih]

theorem map_of_emeet (m1 m2 : List (Var × Ty)) (y : Var) :
    map_of (emeet m1 m2) y =
      (match map_of m1 y with
       | some A => some (match map_of m2 y with | some B => Inter A B | none => A)
       | none => map_of m2 y) := by
  unfold emeet
  rw [map_of_append, map_of_map_dep (fun x A => match map_of m2 x with | some B => Inter A B | none => A)]
  cases map_of m1 y <;> simp

theorem map_of_cons_self (x : Var) (A : Ty) (m : List (Var × Ty)) :
    map_of ((x, A) :: m) x = some A := by simp [map_of]

theorem map_of_cons_ne {x y : Var} (A : Ty) (m : List (Var × Ty)) (h : x ≠ y) :
    map_of ((x, A) :: m) y = map_of m y := by simp [map_of, h]

theorem map_of_SomeD {m : List (Var × Ty)} {x : Var} {A : Ty} (h : map_of m x = some A) :
    (x, A) ∈ m := by
  induction m with
  | nil => simp [map_of] at h
  | cons p m ih =>
    obtain ⟨z, B⟩ := p
    by_cases hz : z = x
    · subst hz; simp [map_of] at h; subst h; simp
    · simp [map_of, hz] at h; exact List.mem_cons_of_mem _ (ih h)

/-! ## Subtyping `≤₀` -/

inductive Sub : Ty → Ty → Prop where
  | s_refl (A : Ty) : Sub A A
  | s_trans {A B C : Ty} : Sub A B → Sub B C → Sub A C
  | s_top (A : Ty) : Sub A Om
  | s_il (A B : Ty) : Sub (Ty.Inter A B) A
  | s_ir (A B : Ty) : Sub (Ty.Inter A B) B
  | s_glb {C A B : Ty} : Sub C A → Sub C B → Sub C (Ty.Inter A B)
  | s_arr {A' A B B' : Ty} : Sub A' A → Sub B B' → Sub (Arr A B) (Arr A' B')
  /-- Isabelle's `s_env`, with the hypothesis split in two (`Exists` cannot be nested in an
  inductive constructor); see `Sub.s_env` for the original form. -/
  | s_env_core {m' m : List (Var × Ty)} {ob' ob : Bool} :
      (∀ x A', map_of m' x = some A' → ∃ A, map_of m x = some A) →
      (∀ x A' A, map_of m' x = some A' → map_of m x = some A → Sub A A') →
      (ob' = true → ob = true) → Sub (Env m ob) (Env m' ob')
  | s_emeet (m1 : List (Var × Ty)) (o1 : Bool) (m2 : List (Var × Ty)) (o2 : Bool) :
      Sub (Ty.Inter (Env m1 o1) (Env m2 o2)) (Env (emeet m1 m2) (o1 || o2))
  | s_omenv : Sub Om (Env [] false)
  | s_envarr {m : List (Var × Ty)} {x : Var} {A : Ty} (ob : Bool) :
      map_of m x = some A → Sub (Env m ob) (Arr (QN x) A)
  | s_arrenv (x : Var) (A : Ty) : Sub (Arr (QN x) A) (Env [(x, A)] false)

infix:50 " ≼ " => Sub

/-- Isabelle's `s_env`. -/
theorem Sub.s_env {m' m : List (Var × Ty)} {ob' ob : Bool}
    (h : ∀ x A', map_of m' x = some A' → ∃ A, map_of m x = some A ∧ A ≼ A')
    (hob : ob' = true → ob = true) : Env m ob ≼ Env m' ob' :=
  .s_env_core (fun x A' hx => let ⟨A, hA, _⟩ := h x A' hx; ⟨A, hA⟩)
    (fun x A' A hx hA => by
      obtain ⟨A2, hA2, hs⟩ := h x A' hx
      rw [hA] at hA2; cases hA2; exact hs) hob

/-- Essential types. -/
def ess : Ty → Prop
  | TV _ => True
  | Om => False
  | Arr _ _ => True
  | Ty.Inter A B => ess A ∨ ess B
  | Env m ob => m ≠ [] ∨ ob = true
  | QN _ => True

theorem ess_down {A B : Ty} (h : A ≼ B) : ess B → ess A := by
  induction h with
  | s_refl => exact id
  | s_trans _ _ ih1 ih2 => exact fun h => ih1 (ih2 h)
  | s_top => simp [ess]
  | s_il => exact fun h => Or.inl h
  | s_ir => exact fun h => Or.inr h
  | s_glb _ _ ih1 ih2 => intro h; rcases h with h | h; exact ih1 h; exact ih2 h
  | s_arr => simp [ess]
  | @s_env_core m' m ob' ob hm _ hob =>
    intro h
    rcases h with h | h
    · cases m' with
      | nil => exact absurd rfl h
      | cons p ps =>
        obtain ⟨x, A'⟩ := p
        obtain ⟨A, hA⟩ := hm x A' (map_of_cons_self _ _ _)
        left
        intro e; subst e; simp [map_of] at hA
    · exact Or.inr (hob h)
  | s_emeet m1 o1 m2 o2 =>
    intro h
    simp only [ess] at h ⊢
    rcases h with h | h
    · by_cases h1 : m1 = []
      · right; left; intro h2; apply h; simp [emeet, h1, h2]
      · left; left; exact h1
    · cases o1 <;> cases o2 <;> simp_all
  | s_omenv => simp [ess]
  | s_envarr ob h =>
    intro _; left; intro e; subst e; simp [map_of] at h
  | s_arrenv => intro _; simp [ess]

theorem sub_env_ext_meet1 (x : Var) (B1 B2 : Ty) (m1 m2 : List (Var × Ty)) (o1 o2 : Bool) :
    Env ((x, Inter B1 B2) :: emeet m1 m2) (o1 || o2) ≼ Env ((x, B1) :: m1) o1 := by
  apply Sub.s_env
  · intro y A' hy
    by_cases h : x = y
    · subst h
      rw [map_of_cons_self] at hy
      cases hy
      exact ⟨_, map_of_cons_self _ _ _, .s_il _ _⟩
    · rw [map_of_cons_ne _ _ h] at hy
      rw [map_of_cons_ne _ _ h, map_of_emeet, hy]
      cases h2 : map_of m2 y with
      | none => exact ⟨_, rfl, .s_refl _⟩
      | some B => exact ⟨_, rfl, .s_il _ _⟩
  · intro h; simp [h]

theorem sub_env_ext_meet2 (x : Var) (B1 B2 : Ty) (m1 m2 : List (Var × Ty)) (o1 o2 : Bool) :
    Env ((x, Inter B1 B2) :: emeet m1 m2) (o1 || o2) ≼ Env ((x, B2) :: m2) o2 := by
  apply Sub.s_env
  · intro y A' hy
    by_cases h : x = y
    · subst h
      rw [map_of_cons_self] at hy
      cases hy
      exact ⟨_, map_of_cons_self _ _ _, .s_ir _ _⟩
    · rw [map_of_cons_ne _ _ h] at hy
      rw [map_of_cons_ne _ _ h, map_of_emeet, hy]
      cases h1 : map_of m1 y with
      | none => exact ⟨_, rfl, .s_refl _⟩
      | some B => exact ⟨_, rfl, .s_ir _ _⟩
  · intro h; simp [h]

/-! ## Typing (contexts are arbitrary types) -/

inductive Hasty : Ty → Trm → Ty → Prop where
  | TVar {C : Ty} {m : List (Var × Ty)} {ob : Bool} {x : Var} {A : Ty} :
      C ≼ Env m ob → map_of m x = some A → Hasty C (var x) A
  | TLam {C : Ty} {m : List (Var × Ty)} {ob : Bool} {x : Var} {A : Ty} {M : Trm} {B : Ty} :
      C ≼ Env m ob → Hasty (Env ((x, A) :: m) ob) M B → Hasty C (lam x M) (Arr A B)
  | TApp {C : Ty} {M : Trm} {A B : Ty} {N : Trm} :
      Hasty C M (Arr A B) → Hasty C N A → Hasty C (app M N) B
  | TId (C : Ty) : Hasty C iden C
  | TExtn {C : Ty} {M : Trm} {A : Ty} {N : Trm} {m : List (Var × Ty)} {ob : Bool} {x : Var} :
      Hasty C M A → Hasty C N (Env m ob) → Hasty C (extn M x N) (Env ((x, A) :: m) ob)
  | TComp {C : Ty} {N : Trm} {D : Ty} {M : Trm} {A : Ty} :
      Hasty C N D → Hasty D M A → Hasty C (comp M N) A
  | TOm (C : Ty) (M : Trm) : Hasty C M Om
  | TInter {C : Ty} {M : Trm} {A B : Ty} :
      Hasty C M A → Hasty C M B → Hasty C M (Inter A B)
  | TSub {C : Ty} {M : Trm} {A B : Ty} : Hasty C M A → A ≼ B → Hasty C M B
  | TNm (C : Ty) (x : Var) : Hasty C (nm x) (QN x)

notation:50 C:51 " ⊢ " M:51 " : " A:51 => Hasty C M A

/-- Types without name types (decision D4: free variables are not names). -/
def qfree : Ty → Prop
  | TV _ => True
  | Om => True
  | Arr A B => qfree A ∧ qfree B
  | Ty.Inter A B => qfree A ∧ qfree B
  | Env m _ => qfreeList m
  | QN _ => False
where
  qfreeList : List (Var × Ty) → Prop
  | [] => True
  | (_, A) :: m => qfree A ∧ qfreeList m

def Typ (M : Trm) : Prop :=
  ∃ m ob A, Hasty (Env m ob) M A ∧ ess A ∧ ∀ p ∈ m, qfree p.2

/-! ## Narrowing of contexts -/

theorem narrowing {C : Ty} {M : Trm} {A : Ty} (h : Hasty C M A) :
    ∀ {C' : Ty}, C' ≼ C → Hasty C' M A := by
  induction h with
  | TVar h1 h2 => exact fun hc => .TVar (.s_trans hc h1) h2
  | TLam h1 h2 _ => exact fun hc => .TLam (.s_trans hc h1) h2
  | TApp _ _ ih1 ih2 => exact fun hc => .TApp (ih1 hc) (ih2 hc)
  | TId => exact fun hc => .TSub (.TId _) hc
  | TExtn _ _ ih1 ih2 => exact fun hc => .TExtn (ih1 hc) (ih2 hc)
  | TComp _ h2 ih1 _ => exact fun hc => .TComp (ih1 hc) h2
  | TOm => exact fun _ => .TOm _ _
  | TInter _ _ ih1 ih2 => exact fun hc => .TInter (ih1 hc) (ih2 hc)
  | TSub _ h2 ih => exact fun hc => .TSub (ih hc) h2
  | TNm => exact fun _ => .TNm _ _

theorem typ_env_om (C : Ty) (M : Trm) : Hasty C M (Env [] false) := .TSub (.TOm _ _) .s_omenv

/-! ## Generation lemmas -/

theorem gen_Id {C A : Ty} {P : Trm} (h : Hasty C P A) : P = iden → C ≼ A := by
  induction h with
  | TId => intro _; exact .s_refl _
  | TOm => intro _; exact .s_top _
  | TInter _ _ ih1 ih2 => intro e; exact .s_glb (ih1 e) (ih2 e)
  | TSub _ h2 ih => intro e; exact .s_trans (ih e) h2
  | _ => intro e; cases e

theorem gen_Comp {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) :
    ∀ {M L : Trm}, P = comp M L → ∃ D, Hasty C L D ∧ Hasty D M A := by
  induction h with
  | TComp h1 h2 _ _ => intro M L e; cases e; exact ⟨_, h1, h2⟩
  | TOm => intro M L _; exact ⟨Om, .TOm _ _, .TOm _ _⟩
  | TInter _ _ ih1 ih2 =>
    intro M L e
    obtain ⟨D1, a1, a2⟩ := ih1 e
    obtain ⟨D2, b1, b2⟩ := ih2 e
    exact ⟨Inter D1 D2, .TInter a1 b1,
      .TInter (narrowing a2 (.s_il _ _)) (narrowing b2 (.s_ir _ _))⟩
  | TSub _ h2 ih =>
    intro M L e
    obtain ⟨D, a1, a2⟩ := ih e
    exact ⟨D, a1, .TSub a2 h2⟩
  | _ => intro M L e; cases e

theorem gen_Extn {C : Ty} {P : Trm} {D : Ty} (h : Hasty C P D) :
    ∀ {N : Trm} {x : Var} {L : Trm}, P = extn N x L →
      ∃ B m ob, Hasty C N B ∧ Hasty C L (Env m ob) ∧ Env ((x, B) :: m) ob ≼ D := by
  induction h with
  | TExtn h1 h2 _ _ => intro N x L e; cases e; exact ⟨_, _, _, h1, h2, .s_refl _⟩
  | TOm =>
    intro N x L _
    exact ⟨Om, [], false, .TOm _ _, typ_env_om _ _, .s_top _⟩
  | TInter _ _ ih1 ih2 =>
    intro N x L e
    obtain ⟨B1, m1, o1, a1, a2, a3⟩ := ih1 e
    obtain ⟨B2, m2, o2, b1, b2, b3⟩ := ih2 e
    refine ⟨Inter B1 B2, emeet m1 m2, o1 || o2, .TInter a1 b1, ?_, ?_⟩
    · exact .TSub (.TInter a2 b2) (.s_emeet _ _ _ _)
    · exact .s_glb (.s_trans (sub_env_ext_meet1 _ _ _ _ _ _ _) a3)
        (.s_trans (sub_env_ext_meet2 _ _ _ _ _ _ _) b3)
  | TSub _ h2 ih =>
    intro N x L e
    obtain ⟨B, m, ob, a1, a2, a3⟩ := ih e
    exact ⟨B, m, ob, a1, a2, .s_trans a3 h2⟩
  | _ => intro N x L e; cases e

theorem gen_Nm {C A : Ty} {P : Trm} (h : Hasty C P A) : ∀ {x : Var}, P = nm x → QN x ≼ A := by
  induction h with
  | TNm => intro x e; cases e; exact .s_refl _
  | TOm => intro _ _; exact .s_top _
  | TInter _ _ ih1 ih2 => intro x e; exact .s_glb (ih1 e) (ih2 e)
  | TSub _ h2 ih => intro x e; exact .s_trans (ih e) h2
  | _ => intro x e; cases e

theorem gen_Var {D : Ty} {P : Trm} {A : Ty} (h : Hasty D P A) :
    ∀ {y : Var}, P = var y →
      (Om ≼ A) ∨ (∃ m ob B, D ≼ Env m ob ∧ map_of m y = some B ∧ B ≼ A) := by
  induction h with
  | TVar h1 h2 => intro y e; cases e; exact Or.inr ⟨_, _, _, h1, h2, .s_refl _⟩
  | TOm => intro y _; exact Or.inl (.s_refl _)
  | TInter _ _ ih1 ih2 =>
    intro y e
    rcases ih1 e with o1 | ⟨m1, o1, B1, c1, l1, b1⟩ <;>
    rcases ih2 e with o2 | ⟨m2, o2, B2, c2, l2, b2⟩
    · exact Or.inl (.s_glb o1 o2)
    · exact Or.inr ⟨m2, o2, B2, c2, l2, .s_glb (.s_trans (.s_top B2) o1) b2⟩
    · exact Or.inr ⟨m1, o1, B1, c1, l1, .s_glb b1 (.s_trans (.s_top B1) o2)⟩
    · refine Or.inr ⟨emeet m1 m2, o1 || o2, Ty.Inter B1 B2, ?_, ?_, ?_⟩
      · exact .s_trans (.s_glb c1 c2) (.s_emeet _ _ _ _)
      · rw [map_of_emeet, l1, l2]
      · exact .s_glb (.s_trans (.s_il _ _) b1) (.s_trans (.s_ir _ _) b2)
  | TSub _ h2 ih =>
    intro y e
    rcases ih e with o | ⟨m, ob, B, c, l, b⟩
    · exact Or.inl (.s_trans o h2)
    · exact Or.inr ⟨m, ob, B, c, l, .s_trans b h2⟩
  | _ => intro y e; cases e

end LambdaPEnvWH
