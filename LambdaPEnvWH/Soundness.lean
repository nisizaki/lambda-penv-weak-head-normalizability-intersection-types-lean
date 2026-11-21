import LambdaPEnvWH.Completeness
import LambdaPEnvWH.Uniform

/-!
# Soundness: `Typ M → CFWHN M`

Port of `Soundness.thy` (λpenv_wh).  The interpretation of `Env m ob` contains both lookup
(`x ∘ e`) and application to names (`e N` for `N →wh* ⌜x⌝`); `I (QN x) = {M | M →wh* nm x}`.
-/

namespace LambdaPEnvWH

open Trm Ty

/-! ## Auxiliary reduction lemmas -/

theorem CFWHN_back {M M' : Trm} (h : Wh M M') (c : CFWHN M') : CFWHN M := by
  obtain ⟨N, r, n, nc⟩ := c
  exact ⟨N, .step h r, n, nc⟩

theorem CFWHN_back_steps {M M' : Trm} (h : WhSteps M M') (c : CFWHN M') : CFWHN M := by
  induction h with
  | refl => exact c
  | step h _ ih => exact CFWHN_back h (ih c)

theorem sig_steps_wh {M N : Trm} (h : Star Sig M N) : WhSteps M N :=
  Star.mono (fun _ _ h => sig_imp_wh h) h

theorem steps_lift {α β : Type} {R : α → α → Prop} {R' : β → β → Prop} {f : α → β}
    (h : ∀ P Q, R P Q → R' (f P) (f Q)) {M N : α} (s : Star R M N) : Star R' (f M) (f N) :=
  Star.map f h s

theorem wh_steps_AppL {M M' : Trm} (N : Trm) (h : WhSteps M M') : WhSteps (app M N) (app M' N) :=
  Star.map (fun P => app P N) (fun _ _ h => wh_AppL N h) h

theorem sig_steps_AppR {N N' : Trm} (M : Trm) (h : Star Sig N N') :
    WhSteps (app M N) (app M N') :=
  Star.map (fun P => app M P) (fun _ _ h => sig_imp_wh (.AppR M h)) h

theorem sig_steps_Lam {M M' : Trm} (x : Var) (h : Star Sig M M') :
    WhSteps (lam x M) (lam x M') :=
  Star.map (fun P => lam x P) (fun _ _ h => sig_imp_wh (.Lam x h)) h

theorem sig_steps_CompL {M M' : Trm} (N : Trm) (h : Star Sig M M') :
    WhSteps (comp M N) (comp M' N) :=
  Star.map (fun P => comp P N) (fun _ _ h => sig_imp_wh (.CompL N h)) h

theorem sig_steps_CompR {N N' : Trm} (M : Trm) (h : Star Sig N N') :
    WhSteps (comp M N) (comp M N') :=
  Star.map (fun P => comp M P) (fun _ _ h => sig_imp_wh (.CompR M h)) h

theorem sig_steps_ExtnL {M M' : Trm} (x : Var) (N : Trm) (h : Star Sig M M') :
    WhSteps (extn M x N) (extn M' x N) :=
  Star.map (fun P => extn P x N) (fun _ _ h => sig_imp_wh (.ExtnL x N h)) h

theorem sig_steps_ExtnR {N N' : Trm} (M : Trm) (x : Var) (h : Star Sig N N') :
    WhSteps (extn M x N) (extn M x N') :=
  Star.map (fun P => extn M x P) (fun _ _ h => sig_imp_wh (.ExtnR M x h)) h

theorem wh_steps_VarR {M M' : Trm} (x : Var) (h : WhSteps M M') :
    WhSteps (comp (var x) M) (comp (var x) M') :=
  Star.map (fun P => comp (var x) P) (fun _ _ h => wh_VarR x h) h

theorem val_CFWHN {M : Trm} (h : val M) : CFWHN M :=
  ⟨M, .refl _, val_WHNF h, val_not_clash h⟩

theorem neu_CFWHN {M : Trm} (h : neu M) : CFWHN M :=
  ⟨M, .refl _, neu_WHNF h, neu_not_clash h⟩

theorem CFWHN_Lam (x : Var) (M : Trm) : CFWHN (lam x M) := by
  obtain ⟨M', s, n⟩ := sig_nf M
  exact CFWHN_back_steps (sig_steps_Lam x s) (val_CFWHN (.VLam x n))

theorem CFWHN_Extn (M : Trm) (x : Var) (N : Trm) : CFWHN (extn M x N) := by
  obtain ⟨M', s1, n1⟩ := sig_nf M
  obtain ⟨N', s2, n2⟩ := sig_nf N
  have r : WhSteps (extn M x N) (extn M' x N') :=
    (sig_steps_ExtnL x N s1).trans (sig_steps_ExtnR M' x s2)
  exact CFWHN_back_steps r (val_CFWHN (.VExtn x n1 n2))

theorem CFWHN_Clo (x : Var) (M e : Trm) : CFWHN (comp (lam x M) e) := by
  obtain ⟨M', s1, n1⟩ := sig_nf M
  obtain ⟨e', s2, n2⟩ := sig_nf e
  have r : WhSteps (comp (lam x M) e) (comp (lam x M') e') := by
    have : Star Sig (lam x M) (lam x M') :=
      Star.map (fun P => lam x P) (fun _ _ h => Sig.Lam x h) s1
    exact (sig_steps_CompL e this).trans (sig_steps_CompR _ s2)
  by_cases he : e' = iden
  · subst he
    have h1 : Wh (comp (lam x M') iden) (lam x M') := sig_imp_wh (.IdR _)
    exact CFWHN_back_steps r (CFWHN_back h1 (val_CFWHN (.VLam x n1)))
  · exact CFWHN_back_steps r (val_CFWHN (.VClo x n1 n2 he))


theorem wh_steps_ArgV {V N N' : Trm} (hV : envh V) (h : WhSteps N N') :
    WhSteps (app V N) (app V N') :=
  Star.map (fun P => app V P) (fun _ _ h => wh_ArgV hV h) h

theorem Nm_CFWHN (x : Var) : CFWHN (nm x) := val_CFWHN (.VNm x)

/-- Weak neutral terms: arguments need not be σ-normal. -/
inductive wneu : Trm → Prop where
  | wneu_var (x : Var) : wneu (var x)
  | wneu_app {M : Trm} (N : Trm) : wneu M → wneu (app M N)
  | wneu_comp {M : Trm} (x : Var) : wneu M → wneu (comp (var x) M)

theorem wneu_reduces {M : Trm} (h : wneu M) : ∃ M', WhSteps M M' ∧ neu M' := by
  induction h with
  | wneu_var x => exact ⟨_, .refl _, .NVar x⟩
  | wneu_app N _ ih =>
    obtain ⟨M', r, n⟩ := ih
    obtain ⟨N', s, nn⟩ := sig_nf N
    have rr : WhSteps (app _ N) (app M' N') :=
      (wh_steps_AppL N r).trans (sig_steps_AppR M' s)
    by_cases hy : ∃ y, N' = nm y
    · obtain ⟨y, rfl⟩ := hy
      exact ⟨comp (var y) M', rr.tail (sig_imp_wh (.AppConst M' y)), .NComp y n⟩
    · exact ⟨app M' N', rr, .NApp n nn (fun y e => hy ⟨y, e⟩)⟩
  | wneu_comp x _ ih =>
    obtain ⟨M', r, n⟩ := ih
    exact ⟨_, wh_steps_VarR x r, .NComp x n⟩

theorem wneu_CFWHN {M : Trm} (h : wneu M) : CFWHN M := by
  obtain ⟨M', r, n⟩ := wneu_reduces h
  exact CFWHN_back_steps r (neu_CFWHN n)

/-! ## Interpretation of types -/

theorem Ty.ind {P : Ty → Prop}
    (tv : ∀ n, P (TV n)) (om : P Om) (arr : ∀ A B, P A → P B → P (Arr A B))
    (inter : ∀ A B, P A → P B → P (Ty.Inter A B))
    (env : ∀ m ob, (∀ x A, (x, A) ∈ m → P A) → P (Env m ob))
    (qn : ∀ x, P (QN x)) : ∀ A, P A
  | TV n => tv n
  | Om => om
  | Arr A B => arr A B (Ty.ind tv om arr inter env qn A) (Ty.ind tv om arr inter env qn B)
  | Ty.Inter A B =>
    inter A B (Ty.ind tv om arr inter env qn A) (Ty.ind tv om arr inter env qn B)
  | Env m ob => env m ob (fun x A h => Ty.ind tv om arr inter env qn A)
  | QN x => qn x
termination_by A => sizeOf A
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have h1 := List.sizeOf_lt_of_mem h; simp at h1; omega)

/-- Realizability interpretation of types (Isabelle `I`; a set of terms is a predicate).
`I (QN x) M` is `M →wh* ⌜x⌝`; `Env` contains lookup and application to names. -/
def I : Ty → Trm → Prop
  | TV _, M => CFWHN M
  | Om, _ => True
  | Arr A B, M => CFWHN M ∧ ∀ N, I A N → I B (app M N)
  | Ty.Inter A B, M => I A M ∧ I B M
  | QN x, M => WhSteps M (nm x)
  | Env m ob, e =>
      ((m ≠ [] ∨ ob = true) → CFWHN e) ∧
      ∀ p (hp : p ∈ m), map_of m p.1 = some p.2 →
        I p.2 (comp (var p.1) e) ∧ ∀ N, WhSteps N (nm p.1) → I p.2 (app e N)
termination_by A => sizeOf A
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (obtain ⟨a, b⟩ := p; have h1 := List.sizeOf_lt_of_mem hp; simp at h1 ⊢; omega)

theorem I_TV (n : Nat) (M : Trm) : I (TV n) M = CFWHN M := by rw [I]
theorem I_Om (M : Trm) : I Om M = True := by rw [I]
theorem I_Arr (A B : Ty) (M : Trm) :
    I (Arr A B) M = (CFWHN M ∧ ∀ N, I A N → I B (app M N)) := by rw [I]
theorem I_Inter (A B : Ty) (M : Trm) : I (Ty.Inter A B) M = (I A M ∧ I B M) := by rw [I]
theorem I_QN (x : Var) (M : Trm) : I (QN x) M = WhSteps M (nm x) := by rw [I]

theorem I_Env {m : List (Var × Ty)} {ob : Bool} {e : Trm} :
    I (Env m ob) e ↔
      ((m ≠ [] ∨ ob = true) → CFWHN e) ∧
      (∀ x A, map_of m x = some A →
        I A (comp (var x) e) ∧ ∀ N, WhSteps N (nm x) → I A (app e N)) := by
  rw [I]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨h1, fun x A hA => h2 (x, A) (map_of_SomeD hA) hA⟩
  · intro ⟨h1, h2⟩
    exact ⟨h1, fun p _ hp => h2 p.1 p.2 hp⟩

theorem I_back {M M' : Trm} {A : Ty} (h : Wh M M') (hI : I A M') : I A M := by
  induction A using Ty.ind generalizing M M' with
  | tv n => rw [I_TV] at *; exact CFWHN_back h hI
  | om => rw [I_Om]; trivial
  | arr A B _ ihB =>
    rw [I_Arr] at *
    exact ⟨CFWHN_back h hI.1, fun N hN => ihB (wh_AppL N h) (hI.2 N hN)⟩
  | inter A B ihA ihB =>
    rw [I_Inter] at *
    exact ⟨ihA h hI.1, ihB h hI.2⟩
  | qn x => rw [I_QN] at *; exact .step h hI
  | env m ob ih =>
    rw [I_Env] at *
    refine ⟨fun hm => CFWHN_back h (hI.1 hm), fun x A l => ?_⟩
    exact ⟨ih x A (map_of_SomeD l) (wh_VarR x h) (hI.2 x A l).1,
      fun N hN => ih x A (map_of_SomeD l) (wh_AppL N h) ((hI.2 x A l).2 N hN)⟩

theorem I_back_steps {M M' : Trm} {A : Ty} (h : WhSteps M M') (hI : I A M') : I A M := by
  induction h with
  | refl => exact hI
  | step h _ ih => exact I_back h (ih hI)

theorem I_fwd {M M' : Trm} {A : Ty} (h : Wh M M') (hI : I A M) : I A M' := by
  induction A using Ty.ind generalizing M M' with
  | tv n => rw [I_TV] at *; exact CFWHN_fwd h hI
  | om => rw [I_Om]; trivial
  | arr A B _ ihB =>
    rw [I_Arr] at *
    exact ⟨CFWHN_fwd h hI.1, fun N hN => ihB (wh_AppL N h) (hI.2 N hN)⟩
  | inter A B ihA ihB =>
    rw [I_Inter] at *
    exact ⟨ihA h hI.1, ihB h hI.2⟩
  | qn x => rw [I_QN] at *; exact Nm_fwd h hI
  | env m ob ih =>
    rw [I_Env] at *
    refine ⟨fun hm => CFWHN_fwd h (hI.1 hm), fun x A l => ?_⟩
    exact ⟨ih x A (map_of_SomeD l) (wh_VarR x h) (hI.2 x A l).1,
      fun N hN => ih x A (map_of_SomeD l) (wh_AppL N h) ((hI.2 x A l).2 N hN)⟩

theorem I_ess {A : Ty} (hA : ess A) {M : Trm} (hI : I A M) : CFWHN M := by
  induction A using Ty.ind generalizing M with
  | tv n => rwa [I_TV] at hI
  | om => exact absurd hA (by simp [ess])
  | arr A B _ _ => rw [I_Arr] at hI; exact hI.1
  | inter A B ihA ihB =>
    rw [I_Inter] at hI
    rcases hA with h | h
    · exact ihA h hI.1
    · exact ihB h hI.2
  | env m ob _ => rw [I_Env] at hI; exact hI.1 hA
  | qn x => rw [I_QN] at hI; exact CFWHN_back_steps hI (Nm_CFWHN x)

theorem qfreeList_mem {m : List (Var × Ty)} (h : qfree.qfreeList m) {x : Var} {A : Ty}
    (hx : (x, A) ∈ m) : qfree A := by
  induction m with
  | nil => cases hx
  | cons p m ih =>
    obtain ⟨y, B⟩ := p
    simp only [qfree.qfreeList] at h
    rcases List.mem_cons.1 hx with e | e
    · cases e; exact h.1
    · exact ih h.2 e

theorem wneu_I {A : Ty} (hq : qfree A) {M : Trm} (hw : wneu M) : I A M := by
  induction A using Ty.ind generalizing M with
  | tv n => rw [I_TV]; exact wneu_CFWHN hw
  | om => rw [I_Om]; trivial
  | arr A B _ ihB =>
    rw [I_Arr]; exact ⟨wneu_CFWHN hw, fun N _ => ihB hq.2 (.wneu_app N hw)⟩
  | inter A B ihA ihB => rw [I_Inter]; exact ⟨ihA hq.1 hw, ihB hq.2 hw⟩
  | qn x => exact hq.elim
  | env m ob ih =>
    rw [I_Env]
    refine ⟨fun _ => wneu_CFWHN hw, fun x A l => ?_⟩
    have hx := map_of_SomeD l
    have qa := qfreeList_mem hq hx
    exact ⟨ih x A hx qa (.wneu_comp x hw), fun N _ => ih x A hx qa (.wneu_app N hw)⟩

theorem Var_I {A : Ty} (hq : qfree A) (x : Var) : I A (var x) := wneu_I hq (.wneu_var x)

/-! ## Monotonicity -/

theorem I_mono {A B : Ty} (h : A ≼ B) : ∀ {M : Trm}, I A M → I B M := by
  induction h with
  | s_refl => exact id
  | s_trans _ _ ih1 ih2 => exact fun h => ih2 (ih1 h)
  | s_top => intro M _; rw [I_Om]; trivial
  | s_il => intro M h; rw [I_Inter] at h; exact h.1
  | s_ir => intro M h; rw [I_Inter] at h; exact h.2
  | s_glb _ _ ih1 ih2 => intro M h; rw [I_Inter]; exact ⟨ih1 h, ih2 h⟩
  | s_arr _ _ ih1 ih2 =>
    intro M h
    rw [I_Arr] at *
    exact ⟨h.1, fun N hN => ih2 (h.2 N (ih1 hN))⟩
  | @s_env_core m' m ob' ob hdom hsub hob ih =>
    intro e he
    rw [I_Env] at he ⊢
    refine ⟨fun hm => he.1 ?_, fun x A' l => ?_⟩
    · rcases hm with hm | hm
      · cases m' with
        | nil => exact absurd rfl hm
        | cons p ps =>
          obtain ⟨x, A'⟩ := p
          obtain ⟨A, hA⟩ := hdom x A' (map_of_cons_self _ _ _)
          left
          intro e; subst e; simp [map_of] at hA
      · exact Or.inr (hob hm)
    · obtain ⟨A, hA⟩ := hdom x A' l
      have k := he.2 x A hA
      exact ⟨ih x A' A l hA k.1, fun N hN => ih x A' A l hA (k.2 N hN)⟩
  | s_emeet m1 o1 m2 o2 =>
    intro e he
    rw [I_Inter, I_Env, I_Env] at he
    obtain ⟨⟨c1, l1⟩, ⟨c2, l2⟩⟩ := he
    rw [I_Env]
    refine ⟨fun hm => ?_, fun x A l => ?_⟩
    · rcases hm with hm | hm
      · by_cases h1 : m1 = []
        · apply c2; left; intro h2; apply hm; simp [emeet, h1, h2]
        · exact c1 (Or.inl h1)
      · cases o1 <;> cases o2 <;> simp_all
    · rw [map_of_emeet] at l
      cases h1 : map_of m1 x with
      | none =>
        rw [h1] at l
        exact l2 x A l
      | some A1 =>
        rw [h1] at l
        cases h2 : map_of m2 x with
        | none => rw [h2] at l; cases l; exact l1 x _ h1
        | some A2 =>
          rw [h2] at l; cases l
          have k1 := l1 x _ h1
          have k2 := l2 x _ h2
          simp only [I_Inter]
          exact ⟨⟨k1.1, k2.1⟩, fun N hN => ⟨k1.2 N hN, k2.2 N hN⟩⟩
  | s_omenv =>
    intro M _
    rw [I_Env]
    exact ⟨fun h => by simp at h, fun x A h => by simp [map_of] at h⟩
  | @s_envarr m x A ob hl =>
    intro e he
    rw [I_Env] at he
    rw [I_Arr]
    have k := he.2 x A hl
    refine ⟨he.1 (Or.inl ?_), fun N hN => ?_⟩
    · intro e; subst e; simp [map_of] at hl
    · rw [I_QN] at hN; exact k.2 N hN
  | s_arrenv x A =>
    intro M hM
    rw [I_Arr] at hM
    obtain ⟨cf, ap⟩ := hM
    rw [I_Env]
    refine ⟨fun _ => cf, fun y B l => ?_⟩
    by_cases hxy : x = y
    · subst hxy
      rw [map_of_cons_self] at l; cases l
      have a1 := ap (nm x) (by rw [I_QN]; exact .refl _)
      exact ⟨I_fwd (sig_imp_wh (.AppConst M x)) a1,
        fun N hN => ap N (by rw [I_QN]; exact hN)⟩
    · rw [map_of_cons_ne _ _ hxy] at l; simp [map_of] at l

/-! ## Realizers -/

theorem Id_I {m : List (Var × Ty)} {ob : Bool} (hq : ∀ p ∈ m, qfree p.2) :
    I (Env m ob) iden := by
  rw [I_Env]
  refine ⟨fun _ => val_CFWHN .VId, fun x A l => ?_⟩
  have qa : qfree A := hq _ (map_of_SomeD l)
  have c : I A (comp (var x) iden) := I_back (sig_imp_wh (.IdR _)) (Var_I qa x)
  refine ⟨c, fun N hN => ?_⟩
  have h1 : WhSteps (app iden N) (app iden (nm x)) := wh_steps_ArgV (V := iden) trivial hN
  exact I_back_steps h1 (I_back (sig_imp_wh (.AppConst iden x)) c)

theorem Extn_I {N e : Trm} {A : Ty} {m : List (Var × Ty)} {ob : Bool} {x : Var}
    (n : I A N) (e' : I (Env m ob) e) : I (Env ((x, A) :: m) ob) (extn N x e) := by
  rw [I_Env]
  refine ⟨fun _ => CFWHN_Extn _ _ _, fun y B l => ?_⟩
  have c : I B (comp (var y) (extn N x e)) := by
    by_cases h : x = y
    · subst h
      rw [map_of_cons_self] at l; cases l
      exact I_back (sig_imp_wh (.VarRef _ _ _)) n
    · rw [map_of_cons_ne _ _ h] at l
      rw [I_Env] at e'
      exact I_back (sig_imp_wh (.VarSkip _ _ h)) (e'.2 y B l).1
  refine ⟨c, fun N' hN' => ?_⟩
  have h1 : WhSteps (app (extn N x e) N') (app (extn N x e) (nm y)) :=
    wh_steps_ArgV (V := extn N x e) trivial hN'
  exact I_back_steps h1 (I_back (sig_imp_wh (.AppConst _ y)) c)

/-! ## Basic lemma -/

def env_app (M e : Trm) : Trm := if e = iden then M else comp M e

theorem env_app_iden (M : Trm) : env_app M iden = M := by simp [env_app]
theorem env_app_ne {M e : Trm} (h : e ≠ iden) : env_app M e = comp M e := by simp [env_app, h]

theorem basic {C : Ty} {M : Trm} {A : Ty} (h : Hasty C M A) :
    ∀ {e : Trm}, I C e → I A (env_app M e) := by
  induction h with
  | @TVar C m ob x A h1 h2 =>
    intro e he
    have := I_mono h1 he
    rw [I_Env] at this
    by_cases h : e = iden
    · subst h; rw [env_app_iden]
      exact I_fwd (sig_imp_wh (.IdR _)) (this.2 x A h2).1
    · rw [env_app_ne h]
      exact (this.2 x A h2).1
  | @TLam C m ob x A M B h1 h2 ih =>
    intro e he
    have em : I (Env m ob) e := I_mono h1 he
    rw [I_Arr]
    refine ⟨?_, fun N n => ?_⟩
    · by_cases h : e = iden
      · subst h; rw [env_app_iden]; exact CFWHN_Lam x M
      · rw [env_app_ne h]; exact CFWHN_Clo x M e
    · by_cases h : e = iden
      · subst h
        rw [env_app_iden]
        have := ih (Extn_I (x := x) n em)
        rw [env_app_ne (by simp)] at this
        exact I_back (beta_h_imp_wh (.C (.Beta2 x M N))) this
      · rw [env_app_ne h]
        have := ih (Extn_I (x := x) n em)
        rw [env_app_ne (by simp)] at this
        exact I_back (beta_h_imp_wh (.C (.Beta1 x M e N))) this
  | @TApp C M A B N _ _ ih1 ih2 =>
    intro e he
    have m := ih1 he
    have n := ih2 he
    rw [I_Arr] at m
    by_cases h : e = iden
    · subst h; rw [env_app_iden] at m n ⊢; exact m.2 _ n
    · rw [env_app_ne h] at m n ⊢
      have := m.2 _ n
      exact I_back (sig_imp_wh (.DApp _ _ _)) this
  | TId C =>
    intro e he
    by_cases h : e = iden
    · subst h; rw [env_app_iden]; exact he
    · rw [env_app_ne h]; exact I_back (sig_imp_wh (.IdL _)) he
  | @TExtn C M A N m ob x _ _ ih1 ih2 =>
    intro e he
    have m' := ih1 he
    have n := ih2 he
    by_cases h : e = iden
    · subst h; rw [env_app_iden] at m' n ⊢; exact Extn_I m' n
    · rw [env_app_ne h] at m' n ⊢
      exact I_back (sig_imp_wh (.DExtn _ _ _ _)) (Extn_I m' n)
  | @TComp C N D M A _ _ ih1 ih2 =>
    intro e he
    by_cases h : e = iden
    · subst h
      rw [env_app_iden] at *
      have n : I D N := by have := ih1 he; rwa [env_app_iden] at this
      have := ih2 n
      by_cases hN : N = iden
      · subst hN
        rw [env_app_iden] at this
        exact I_back (sig_imp_wh (.IdR _)) this
      · rwa [env_app_ne hN] at this
    · have n : I D (comp N e) := by have := ih1 he; rwa [env_app_ne h] at this
      have := ih2 n
      rw [env_app_ne (by simp)] at this
      rw [env_app_ne h]
      exact I_back (sig_imp_wh (.Ass _ _ _)) this
  | TOm => intro _ _; rw [I_Om]; trivial
  | TInter _ _ ih1 ih2 => intro e he; rw [I_Inter]; exact ⟨ih1 he, ih2 he⟩
  | TSub _ hs ih => intro e he; exact I_mono hs (ih he)
  | TNm C x =>
    intro e he
    by_cases h : e = iden
    · subst h; rw [env_app_iden, I_QN]; exact .refl _
    · rw [env_app_ne h, I_QN]
      exact .single (sig_imp_wh (.ConstComp x e))

theorem soundness {M : Trm} (h : Typ M) : CFWHN M := by
  obtain ⟨m, ob, A, t, e, q⟩ := h
  have := basic t (Id_I (ob := ob) q)
  rw [env_app_iden] at this
  exact I_ess e this

end LambdaPEnvWH
