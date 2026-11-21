/-!
# Abstract rewriting (minimal)

Port of `ARS.thy`.
-/

namespace LambdaPEnvWH

/-- Reflexive-transitive closure. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Star R a a
  | step {a b c : α} : R a b → Star R b c → Star R a c

namespace Star
variable {α : Type} {R : α → α → Prop}

theorem single {a b : α} (h : R a b) : Star R a b := .step h (.refl b)

theorem trans {a b c : α} (h₁ : Star R a b) (h₂ : Star R b c) : Star R a c := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem tail {a b c : α} (h₁ : Star R a b) (h₂ : R b c) : Star R a c :=
  h₁.trans (single h₂)

theorem mono {S : α → α → Prop} (hRS : ∀ a b, R a b → S a b) {a b : α} (h : Star R a b) :
    Star S a b := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (hRS _ _ h) ih

theorem map {β : Type} {S : β → β → Prop} (f : α → β) (hf : ∀ a b, R a b → S (f a) (f b))
    {a b : α} (h : Star R a b) : Star S (f a) (f b) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (hf _ _ h) ih

end Star

def normal {α : Type} (R : α → α → Prop) (a : α) : Prop := ∀ b, ¬ R a b

theorem normal_star {α : Type} {R : α → α → Prop} {a b : α} (hn : normal R a)
    (h : Star R a b) : b = a := by
  cases h with
  | refl => rfl
  | step h _ => exact absurd h (hn _)

/-- Strong normalization at a point: accessibility for the converse relation. -/
def SN_at {α : Type} (R : α → α → Prop) (a : α) : Prop := Acc (fun b a => R a b) a

theorem SN_at.intro {α : Type} {R : α → α → Prop} {a : α}
    (h : ∀ b, R a b → SN_at R b) : SN_at R a := Acc.intro a h

theorem SN_at.step {α : Type} {R : α → α → Prop} {a b : α}
    (h : SN_at R a) (hr : R a b) : SN_at R b := by
  cases h with
  | intro _ h => exact h b hr

theorem SN_at.induct {α : Type} {R : α → α → Prop} {P : α → Prop} {a : α}
    (h : SN_at R a) (step : ∀ a, SN_at R a → (∀ b, R a b → P b) → P a) : P a := by
  induction h with
  | intro x hx ih => exact step x (Acc.intro x hx) ih

theorem SN_at.star {α : Type} {R : α → α → Prop} {a b : α}
    (h : SN_at R a) (hr : Star R a b) : SN_at R b := by
  induction hr with
  | refl => exact h
  | step h₁ _ ih => exact ih (h.step h₁)

theorem SN_at_normal {α : Type} {R : α → α → Prop} {a : α} (h : normal R a) : SN_at R a :=
  SN_at.intro fun b hb => absurd hb (h b)

theorem SN_at.no_infinite {α : Type} {R : α → α → Prop} {a : α} (h : SN_at R a) :
    ¬ ∃ f : Nat → α, f 0 = a ∧ ∀ i, R (f i) (f (i + 1)) := by
  induction h with
  | intro x _ ih =>
    rintro ⟨f, hf0, hf⟩
    exact ih (f 1) (hf0 ▸ hf 0) ⟨fun i => f (i + 1), rfl, fun i => hf (i + 1)⟩

end LambdaPEnvWH
