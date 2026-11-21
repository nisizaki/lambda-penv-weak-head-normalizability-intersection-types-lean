import LambdaPEnvWH.ARS

/-!
# Pure λ-calculus (de Bruijn) and weak-head reduction

Port of `Lambda.thy`.

Definitions of `lift` and `subst` follow the Isabelle distribution
(`HOL/Proofs/Lambda/Lambda.thy`), with constructors renamed.

Adaptation: the Isabelle notation `t[s/k]` is the function `subst t s k`;
`rtranclp hred` is `Star hred`.
-/

namespace LambdaPEnvWH

inductive dB where
  | DVar : Nat → dB
  | DApp : dB → dB → dB
  | DAbs : dB → dB
  deriving DecidableEq

open dB

def lift : dB → Nat → dB
  | DVar i, k => if i < k then DVar i else DVar (i + 1)
  | DApp s t, k => DApp (lift s k) (lift t k)
  | DAbs s, k => DAbs (lift s (k + 1))

/-- `subst t s k` is Isabelle's `t[s/k]`. -/
def subst : dB → dB → Nat → dB
  | DVar i, s, k => if k < i then DVar (i - 1) else if i = k then s else DVar i
  | DApp t u, s, k => DApp (subst t s k) (subst u s k)
  | DAbs t, s, k => DAbs (subst t (lift s 0) (k + 1))

theorem subst_Var (i : Nat) (s : dB) (k : Nat) :
    subst (DVar i) s k = (if k < i then DVar (i - 1) else if i = k then s else DVar i) := rfl

theorem subst_App (t u s : dB) (k : Nat) :
    subst (DApp t u) s k = DApp (subst t s k) (subst u s k) := rfl

theorem subst_Abs (t s : dB) (k : Nat) :
    subst (DAbs t) s k = DAbs (subst t (lift s 0) (k + 1)) := rfl

@[simp] theorem lift_Var (i k : Nat) :
    lift (DVar i) k = (if i < k then DVar i else DVar (i + 1)) := rfl
@[simp] theorem lift_App (s t : dB) (k : Nat) :
    lift (DApp s t) k = DApp (lift s k) (lift t k) := rfl
@[simp] theorem lift_Abs (s : dB) (k : Nat) :
    lift (DAbs s) k = DAbs (lift s (k + 1)) := rfl
attribute [simp] subst_App subst_Abs

@[simp] theorem subst_eq (k : Nat) (u : dB) : subst (DVar k) u k = u := by
  simp [subst_Var]

@[simp] theorem subst_gt {i j : Nat} (u : dB) (h : i < j) :
    subst (DVar j) u i = DVar (j - 1) := by
  simp [subst_Var, h]

@[simp] theorem subst_lt {i j : Nat} (u : dB) (h : j < i) :
    subst (DVar j) u i = DVar j := by
  have : j ≠ i := by omega
  simp [subst_Var, this, Nat.not_lt_of_gt h]

theorem lift_lift (t : dB) : ∀ {i k : Nat}, i < k + 1 →
    lift (lift t i) (k + 1) = lift (lift t k) i := by
  induction t with
  | DVar j =>
    intro i k h
    simp only [lift_Var]
    (repeat' split) <;> simp_all [lift_Var] <;> (repeat' split) <;> (try simp_all) <;> omega
  | DApp s t ihs iht => intro i k h; simp [ihs h, iht h]
  | DAbs s ih => intro i k h; simp [ih (by omega : i + 1 < k + 1 + 1)]

theorem lift_subst_lt (t : dB) : ∀ {i j : Nat} {s : dB}, i < j + 1 →
    lift (subst t s j) i = subst (lift t i) (lift s i) (j + 1) := by
  induction t with
  | DVar x =>
    intro i j s h
    simp only [subst_Var, lift_Var]
    (repeat' split) <;> simp_all [subst_Var, lift_Var] <;> (repeat' split) <;> (try simp_all) <;> omega
  | DApp a b iha ihb => intro i j s h; simp [iha h, ihb h]
  | DAbs a ih =>
    intro i j s h
    simp [ih (by omega : i + 1 < j + 1 + 1), lift_lift s (by omega : 0 < i + 1)]

@[simp] theorem subst_lift (t : dB) : ∀ {k : Nat} {s : dB}, subst (lift t k) s k = t := by
  induction t with
  | DVar i =>
    intro k s
    simp only [lift_Var]
    (repeat' split) <;> simp_all [subst_Var] <;> omega
  | DApp a b iha ihb => intro k s; simp [iha, ihb]
  | DAbs a ih => intro k s; simp [ih]

/-! ### Weak-head reduction -/

inductive hred : dB → dB → Prop where
  | hbeta (s t : dB) : hred (DApp (DAbs s) t) (subst s t 0)
  | happ {s s' : dB} (t : dB) : hred s s' → hred (DApp s t) (DApp s' t)

theorem DAbs_no_step {s t : dB} : hred (DAbs s) t → False := by
  intro h; cases h

theorem hred_det {s t u : dB} (h : hred s t) : hred s u → t = u := by
  induction h generalizing u with
  | hbeta s t =>
    intro h2
    cases h2 with
    | hbeta => rfl
    | happ _ h => exact (DAbs_no_step h).elim
  | happ t h ih =>
    intro h2
    cases h2 with
    | hbeta => exact (DAbs_no_step h).elim
    | happ _ h' => rw [ih h']

def lam_WHN (t : dB) : Prop := ∃ u, Star hred t u ∧ normal hred u

/-- Number of steps to the normal form (unique by determinism). -/
inductive hdist : dB → Nat → Prop where
  | hd0 {t : dB} : normal hred t → hdist t 0
  | hdS {t u : dB} {n : Nat} : hred t u → hdist u n → hdist t (n + 1)

theorem lam_WHN_hdist {t : dB} (h : lam_WHN t) : ∃ n, hdist t n := by
  obtain ⟨u, r, nf⟩ := h
  induction r with
  | refl => exact ⟨0, .hd0 nf⟩
  | step h _ ih => obtain ⟨n, hn⟩ := ih nf; exact ⟨n + 1, .hdS h hn⟩

theorem hdist_step {t u : dB} {n : Nat} (h : hdist t n) (hr : hred t u) :
    ∃ m, n = m + 1 ∧ hdist u m := by
  cases h with
  | hd0 hn => exact absurd hr (hn _)
  | hdS h' hd => rw [hred_det hr h']; exact ⟨_, rfl, hd⟩

end LambdaPEnvWH
