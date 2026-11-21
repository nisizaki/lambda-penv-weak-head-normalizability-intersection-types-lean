import LambdaPEnvWH.Reduction

/-!
# Confluence of σ-reduction

Port of `Sig_Confluence.thy`: Newman's lemma, congruences and joinability, inversion lemmas,
root steps against arbitrary steps, local confluence of σ by critical pairs, and confluence.
-/

namespace LambdaPEnvWH

open Trm

/-! ## Newman's lemma -/

theorem newman {α : Type} {R : α → α → Prop}
    (loc : ∀ a b c, R a b → R a c → ∃ d, Star R b d ∧ Star R c d)
    {a : α} (sn : SN_at R a) :
    ∀ b c, Star R a b → Star R a c → ∃ d, Star R b d ∧ Star R c d := by
  refine SN_at.induct (P := fun a => ∀ b c, Star R a b → Star R a c → ∃ d, Star R b d ∧ Star R c d)
    sn ?_
  intro a _ ih
  · intro b c ab ac
    cases ab with
    | refl => exact ⟨c, ac, .refl _⟩
    | step ab1 b1b =>
      rename_i b1
      cases ac with
      | refl => exact ⟨b, .refl _, .step ab1 b1b⟩
      | step ac1 c1c =>
        rename_i c1
        obtain ⟨d0, d1, d2⟩ := loc _ _ _ ab1 ac1
        obtain ⟨e, e1, e2⟩ := ih b1 ab1 b d0 b1b d1
        obtain ⟨f, f1, f2⟩ := ih c1 ac1 c e c1c (d2.trans e2)
        exact ⟨f, e1.trans f2, f1⟩

/-! ## Congruences and joinability -/

/-- Isabelle abbreviation `sst = sig⁺⁺*`. -/
abbrev sst : Trm → Trm → Prop := Star Sig

/-- Joinability under σ. -/
def jn (A B : Trm) : Prop := ∃ P, sst A P ∧ sst B P

theorem jn_refl (A : Trm) : jn A A := ⟨A, .refl _, .refl _⟩
theorem jn_sym {A B : Trm} (h : jn A B) : jn B A := by
  obtain ⟨P, h1, h2⟩ := h; exact ⟨P, h2, h1⟩
theorem jn_stepL {A A' B : Trm} (h : Sig A A') (h2 : jn A' B) : jn A B := by
  obtain ⟨P, h1, h3⟩ := h2; exact ⟨P, .step h h1, h3⟩
theorem jn_stepR {A B B' : Trm} (h : Sig B B') (h2 : jn A B') : jn A B := by
  obtain ⟨P, h1, h3⟩ := h2; exact ⟨P, h1, .step h h3⟩

theorem sc_AppL {M M' : Trm} (L : Trm) (h : sst M M') : sst (app M L) (app M' L) :=
  Star.map (fun M => app M L) (fun _ _ h => .AppL L h) h
theorem sc_AppR {M M' : Trm} (L : Trm) (h : sst M M') : sst (app L M) (app L M') :=
  Star.map (fun M => app L M) (fun _ _ h => .AppR L h) h
theorem sc_Lam {M M' : Trm} (x : Var) (h : sst M M') : sst (lam x M) (lam x M') :=
  Star.map (fun M => lam x M) (fun _ _ h => .Lam x h) h
theorem sc_CompL {M M' : Trm} (L : Trm) (h : sst M M') : sst (comp M L) (comp M' L) :=
  Star.map (fun M => comp M L) (fun _ _ h => .CompL L h) h
theorem sc_CompR {M M' : Trm} (L : Trm) (h : sst M M') : sst (comp L M) (comp L M') :=
  Star.map (fun M => comp L M) (fun _ _ h => .CompR L h) h
theorem sc_ExtnL {M M' : Trm} (x : Var) (L : Trm) (h : sst M M') :
    sst (extn M x L) (extn M' x L) :=
  Star.map (fun M => extn M x L) (fun _ _ h => .ExtnL x L h) h
theorem sc_ExtnR {M M' : Trm} (L : Trm) (x : Var) (h : sst M M') :
    sst (extn L x M) (extn L x M') :=
  Star.map (fun M => extn L x M) (fun _ _ h => .ExtnR L x h) h

theorem jn_AppL {A B : Trm} (L : Trm) (h : jn A B) : jn (app A L) (app B L) := by
  obtain ⟨P, h1, h2⟩ := h; exact ⟨_, sc_AppL L h1, sc_AppL L h2⟩
theorem jn_AppR {A B : Trm} (L : Trm) (h : jn A B) : jn (app L A) (app L B) := by
  obtain ⟨P, h1, h2⟩ := h; exact ⟨_, sc_AppR L h1, sc_AppR L h2⟩
theorem jn_Lam {A B : Trm} (x : Var) (h : jn A B) : jn (lam x A) (lam x B) := by
  obtain ⟨P, h1, h2⟩ := h; exact ⟨_, sc_Lam x h1, sc_Lam x h2⟩
theorem jn_CompL {A B : Trm} (L : Trm) (h : jn A B) : jn (comp A L) (comp B L) := by
  obtain ⟨P, h1, h2⟩ := h; exact ⟨_, sc_CompL L h1, sc_CompL L h2⟩
theorem jn_CompR {A B : Trm} (L : Trm) (h : jn A B) : jn (comp L A) (comp L B) := by
  obtain ⟨P, h1, h2⟩ := h; exact ⟨_, sc_CompR L h1, sc_CompR L h2⟩
theorem jn_ExtnL {A B : Trm} (x : Var) (L : Trm) (h : jn A B) :
    jn (extn A x L) (extn B x L) := by
  obtain ⟨P, h1, h2⟩ := h; exact ⟨_, sc_ExtnL x L h1, sc_ExtnL x L h2⟩
theorem jn_ExtnR {A B : Trm} (L : Trm) (x : Var) (h : jn A B) :
    jn (extn L x A) (extn L x B) := by
  obtain ⟨P, h1, h2⟩ := h; exact ⟨_, sc_ExtnR L x h1, sc_ExtnR L x h2⟩

/-! ## Inversion lemmas -/

theorem sig_Var_no (x : Var) (Y : Trm) : ¬ Sig (var x) Y := by
  intro h; cases h
theorem sig_Id_no (Y : Trm) : ¬ Sig iden Y := by
  intro h; cases h

theorem sig_Nm_no (x : Var) (Y : Trm) : ¬ Sig (nm x) Y := by
  intro h; cases h

theorem inv_App {A B X : Trm} (h : Sig (app A B) X) :
    (∃ A', Sig A A' ∧ X = app A' B) ∨ (∃ B', Sig B B' ∧ X = app A B') ∨
    (∃ x, B = nm x ∧ X = comp (var x) A) := by
  cases h with
  | AppL _ h => exact .inl ⟨_, h, rfl⟩
  | AppR _ h => exact .inr (.inl ⟨_, h, rfl⟩)
  | AppConst => exact .inr (.inr ⟨_, rfl, rfl⟩)

theorem inv_Lam {x : Var} {A X : Trm} (h : Sig (lam x A) X) : ∃ A', Sig A A' ∧ X = lam x A' := by
  cases h with
  | Lam _ h => exact ⟨_, h, rfl⟩

theorem inv_Extn {A B X : Trm} {x : Var} (h : Sig (extn A x B) X) :
    (∃ A', Sig A A' ∧ X = extn A' x B) ∨ (∃ B', Sig B B' ∧ X = extn A x B') := by
  cases h with
  | ExtnL _ _ h => exact .inl ⟨_, h, rfl⟩
  | ExtnR _ _ h => exact .inr ⟨_, h, rfl⟩

inductive rt : Trm → Trm → Prop where
  | Ass (L M N : Trm) : rt (comp (comp L M) N) (comp L (comp M N))
  | IdL (M : Trm) : rt (comp iden M) M
  | IdR (M : Trm) : rt (comp M iden) M
  | DExtn (L : Trm) (x : Var) (M N : Trm) :
      rt (comp (extn L x M) N) (extn (comp L N) x (comp M N))
  | VarRef (x : Var) (M N : Trm) : rt (comp (var x) (extn M x N)) M
  | VarSkip {x y : Var} (M N : Trm) : x ≠ y → rt (comp (var y) (extn M x N)) (comp (var y) N)
  | DApp (M1 M2 N : Trm) : rt (comp (app M1 M2) N) (app (comp M1 N) (comp M2 N))
  | ConstComp (x : Var) (L : Trm) : rt (comp (nm x) L) (nm x)

theorem rt_sig {A B : Trm} (h : rt A B) : Sig A B := by
  cases h <;> constructor <;> assumption

theorem inv_Comp_rt {A B X : Trm} (h : Sig (comp A B) X) :
    rt (comp A B) X ∨ (∃ A', Sig A A' ∧ X = comp A' B) ∨ (∃ B', Sig B B' ∧ X = comp A B') := by
  cases h with
  | Ass => exact .inl (.Ass ..)
  | IdL => exact .inl (.IdL _)
  | IdR => exact .inl (.IdR _)
  | DExtn => exact .inl (.DExtn ..)
  | VarRef => exact .inl (.VarRef ..)
  | VarSkip _ _ h => exact .inl (.VarSkip _ _ h)
  | DApp => exact .inl (.DApp ..)
  | ConstComp => exact .inl (.ConstComp ..)
  | CompL _ h => exact .inr (.inl ⟨_, h, rfl⟩)
  | CompR _ h => exact .inr (.inr ⟨_, h, rfl⟩)


/-! ## Root steps against arbitrary steps -/

/-- Perform one σ-step (root or congruence) on the goal's `Sig _ ?_`, then continue with `k`. -/
local syntax "sg_then " tactic : tactic
local macro_rules
  | `(tactic| sg_then $k) =>
    `(tactic| first
    | (assumption; $k) | (apply Sig.Ass; $k) | (apply Sig.IdL; $k) | (apply Sig.IdR; $k) | (apply Sig.DExtn; $k)
    | (apply Sig.VarRef; $k) | (apply Sig.VarSkip; assumption; $k)
    | (apply Sig.DApp; $k) | (apply Sig.AppConst; $k) | (apply Sig.ConstComp; $k)
    | (apply Sig.AppL; sg_then $k) | (apply Sig.AppR; sg_then $k) | (apply Sig.Lam; sg_then $k)
    | (apply Sig.CompL; sg_then $k) | (apply Sig.CompR; sg_then $k)
    | (apply Sig.ExtnL; sg_then $k) | (apply Sig.ExtnR; sg_then $k))

local macro "j0" : tactic => `(tactic| exact jn_refl _)
local macro "j1" : tactic => `(tactic| first
  | (j0)
  | (apply jn_stepL; sg_then (j0))
  | (apply jn_stepR; sg_then (j0)))
local macro "j2" : tactic => `(tactic| first
  | (j0)
  | (apply jn_stepL; sg_then (j1))
  | (apply jn_stepR; sg_then (j1)))
local macro "j3" : tactic => `(tactic| first
  | (j0)
  | (apply jn_stepL; sg_then (j2))
  | (apply jn_stepR; sg_then (j2)))
local macro "j4" : tactic => `(tactic| first
  | (j0)
  | (apply jn_stepL; sg_then (j3))
  | (apply jn_stepR; sg_then (j3)))

theorem inv_Comp {A B X : Trm} (h : Sig (comp A B) X) :
    (∃ L M, A = comp L M ∧ X = comp L (comp M B)) ∨
    (A = iden ∧ X = B) ∨ (B = iden ∧ X = A) ∨
    (∃ L x M, A = extn L x M ∧ X = extn (comp L B) x (comp M B)) ∨
    (∃ x M N, A = var x ∧ B = extn M x N ∧ X = M) ∨
    (∃ x y M N, x ≠ y ∧ A = var y ∧ B = extn M x N ∧ X = comp (var y) N) ∨
    (∃ M1 M2, A = app M1 M2 ∧ X = app (comp M1 B) (comp M2 B)) ∨
    (∃ x, A = nm x ∧ X = nm x) ∨
    (∃ A', Sig A A' ∧ X = comp A' B) ∨ (∃ B', Sig B B' ∧ X = comp A B') := by
  cases h with
  | Ass => exact .inl ⟨_, _, rfl, rfl⟩
  | IdL => exact .inr (.inl ⟨rfl, rfl⟩)
  | IdR => exact .inr (.inr (.inl ⟨rfl, rfl⟩))
  | DExtn => exact .inr (.inr (.inr (.inl ⟨_, _, _, rfl, rfl⟩)))
  | VarRef => exact .inr (.inr (.inr (.inr (.inl ⟨_, _, _, rfl, rfl, rfl⟩))))
  | VarSkip _ _ h =>
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, h, rfl, rfl, rfl⟩)))))
  | DApp => exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, rfl⟩))))))
  | ConstComp => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, rfl, rfl⟩)))))))
  | CompL _ h => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, h, rfl⟩))))))))
  | CompR _ h => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨_, h, rfl⟩))))))))

theorem r_Ass (L M N X : Trm) (h : Sig (comp (comp L M) N) X) : jn (comp L (comp M N)) X := by
  cases h with
  | Ass => j0
  | IdR => j4
  | CompL _ h => cases h <;> j4
  | CompR _ h => j4

theorem r_IdL (M X : Trm) (h : Sig (comp iden M) X) : jn M X := by
  cases h with
  | IdL => j0
  | IdR => j4
  | CompL _ h => cases h
  | CompR _ h => j4

theorem r_IdR (M X : Trm) (h : Sig (comp M iden) X) : jn M X := by
  cases h with
  | Ass => j4
  | IdL => j0
  | IdR => j0
  | DExtn => j4
  | DApp => j4
  | ConstComp => j0
  | CompL _ h => j4
  | CompR _ h => cases h

theorem r_DExtn (L : Trm) (x : Var) (M N X : Trm) (h : Sig (comp (extn L x M) N) X) :
    jn (extn (comp L N) x (comp M N)) X := by
  cases h with
  | IdR => j4
  | DExtn => j0
  | CompL _ h => cases h <;> j4
  | CompR _ h => j4

theorem r_VarRef (x : Var) (M N X : Trm) (h : Sig (comp (var x) (extn M x N)) X) : jn M X := by
  cases h with
  | VarRef => j0
  | VarSkip _ _ h => exact absurd rfl h
  | CompL _ h => cases h
  | CompR _ h => cases h <;> j4

theorem r_VarSkip {x y : Var} (M N X : Trm) (hxy : x ≠ y)
    (h : Sig (comp (var y) (extn M x N)) X) : jn (comp (var y) N) X := by
  cases h with
  | VarRef => exact absurd rfl hxy
  | VarSkip => j0
  | CompL _ h => cases h
  | CompR _ h => cases h <;> j4

theorem r_DApp (M1 M2 N X : Trm) (h : Sig (comp (app M1 M2) N) X) :
    jn (app (comp M1 N) (comp M2 N)) X := by
  cases h with
  | IdR => j4
  | DApp => j0
  | CompL _ h => cases h <;> j4
  | CompR _ h => j4

theorem r_ConstComp (x : Var) (L X : Trm) (h : Sig (comp (nm x) L) X) : jn (nm x) X := by
  cases h with
  | IdR => j0
  | ConstComp => j0
  | CompL _ h => exact absurd h (sig_Nm_no _ _)
  | CompR _ h => j4

theorem root_join {A B X : Trm} (hr : rt A B) (h : Sig A X) : jn B X := by
  cases hr with
  | Ass => exact r_Ass _ _ _ _ h
  | IdL => exact r_IdL _ _ h
  | IdR => exact r_IdR _ _ h
  | DExtn => exact r_DExtn _ _ _ _ _ h
  | VarRef => exact r_VarRef _ _ _ _ h
  | VarSkip _ _ hxy => exact r_VarSkip _ _ _ hxy h
  | DApp => exact r_DApp _ _ _ _ h
  | ConstComp => exact r_ConstComp _ _ _ h

/-! ## Local confluence and confluence -/

theorem lc {M N1 : Trm} (h1 : Sig M N1) : ∀ N2, Sig M N2 → jn N1 N2 := by
  induction h1 with
  | Ass L M N => exact fun X h => r_Ass L M N X h
  | IdL M => exact fun X h => r_IdL M X h
  | IdR M => exact fun X h => r_IdR M X h
  | DExtn L x M N => exact fun X h => r_DExtn L x M N X h
  | VarRef x M N => exact fun X h => r_VarRef x M N X h
  | @VarSkip x y M N hxy => exact fun X h => r_VarSkip M N X hxy h
  | DApp M1 M2 N => exact fun X h => r_DApp M1 M2 N X h
  | AppConst M x =>
    intro X hX
    rcases inv_App hX with ⟨A', c1, rfl⟩ | ⟨B', c1, rfl⟩ | ⟨y, hy, rfl⟩
    · j2
    · exact absurd c1 (sig_Nm_no _ _)
    · cases hy; exact jn_refl _
  | ConstComp x L => exact fun X h => r_ConstComp x L X h
  | @AppL M N L h ih =>
    intro X hX
    rcases inv_App hX with ⟨A', c1, rfl⟩ | ⟨B', c1, rfl⟩ | ⟨x, rfl, rfl⟩
    · exact jn_AppL L (ih A' c1)
    · j2
    · j2
  | @AppR M N L h ih =>
    intro X hX
    rcases inv_App hX with ⟨A', c1, rfl⟩ | ⟨B', c1, rfl⟩ | ⟨x, rfl, rfl⟩
    · j2
    · exact jn_AppR L (ih B' c1)
    · exact absurd h (sig_Nm_no _ _)
  | @Lam M N x h ih =>
    intro X hX
    obtain ⟨A', c1, rfl⟩ := inv_Lam hX
    exact jn_Lam x (ih A' c1)
  | @CompL M N L h ih =>
    intro X hX
    rcases inv_Comp_rt hX with hr | ⟨A', c1, rfl⟩ | ⟨B', c1, rfl⟩
    · exact jn_sym (root_join hr (.CompL L h))
    · exact jn_CompL L (ih A' c1)
    · j2
  | @CompR M N L h ih =>
    intro X hX
    rcases inv_Comp_rt hX with hr | ⟨A', c1, rfl⟩ | ⟨B', c1, rfl⟩
    · exact jn_sym (root_join hr (.CompR L h))
    · j2
    · exact jn_CompR L (ih B' c1)
  | @ExtnL M N x L h ih =>
    intro X hX
    rcases inv_Extn hX with ⟨A', c1, rfl⟩ | ⟨B', c1, rfl⟩
    · exact jn_ExtnL x L (ih A' c1)
    · j2
  | @ExtnR M N L x h ih =>
    intro X hX
    rcases inv_Extn hX with ⟨A', c1, rfl⟩ | ⟨B', c1, rfl⟩
    · j2
    · exact jn_ExtnR L x (ih B' c1)

theorem sig_local_confluent {M N1 N2 : Trm} (h1 : Sig M N1) (h2 : Sig M N2) :
    ∃ P, Star Sig N1 P ∧ Star Sig N2 P := lc h1 N2 h2

theorem sig_confluent {M N1 N2 : Trm} (h1 : Star Sig M N1) (h2 : Star Sig M N2) :
    ∃ P, Star Sig N1 P ∧ Star Sig N2 P :=
  newman (fun _ _ _ hb hc => sig_local_confluent hb hc) (sig_SN M) N1 N2 h1 h2

end LambdaPEnvWH
