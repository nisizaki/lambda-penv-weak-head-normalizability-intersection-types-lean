import LambdaPEnvWH.Sig_Confluence
import LambdaPEnvWH.WHNF_Classes

/-!
# Uniform normalization (no typing involved)

Port of `Uniform.thy` (λpenv_wh): determinism of head β, commutation of σ with `BetaC`
and `BetaH`, the deterministic chain, uniqueness of WHNFs, and forward closure.
-/

namespace LambdaPEnvWH

open Trm


/-! ## Head β is deterministic -/

theorem c_no_var {x : Var} {N : Trm} (h : BetaC (var x) N) : False := by cases h
theorem c_no_iden {N : Trm} (h : BetaC iden N) : False := by cases h
theorem c_no_nm {x : Var} {N : Trm} (h : BetaC (nm x) N) : False := by cases h
theorem c_no_lam {x : Var} {M N : Trm} (h : BetaC (lam x M) N) : False := by cases h
theorem c_no_extn {M L N : Trm} {x : Var} (h : BetaC (extn M x L) N) : False := by cases h
theorem c_no_clo {x : Var} {M L N : Trm} (h : BetaC (comp (lam x M) L) N) : False := by
  cases h with
  | CompL _ h' => exact c_no_lam h'

theorem h_no_var {x : Var} {N : Trm} (h : BetaH (var x) N) : False := by
  cases h with
  | C h' => exact c_no_var h'
theorem h_no_iden {N : Trm} (h : BetaH iden N) : False := by
  cases h with
  | C h' => exact c_no_iden h'
theorem h_no_nm {x : Var} {N : Trm} (h : BetaH (nm x) N) : False := by
  cases h with
  | C h' => exact c_no_nm h'
theorem h_no_lam {x : Var} {M N : Trm} (h : BetaH (lam x M) N) : False := by
  cases h with
  | C h' => exact c_no_lam h'
theorem h_no_extn {M L N : Trm} {x : Var} (h : BetaH (extn M x L) N) : False := by
  cases h with
  | C h' => exact c_no_extn h'
theorem h_no_clo {x : Var} {M L N : Trm} (h : BetaH (comp (lam x M) L) N) : False := by
  cases h with
  | C h' => exact c_no_clo h'

theorem envh_no_c {V N : Trm} (hV : envh V) (h : BetaC V N) : False := by
  cases V with
  | iden => exact c_no_iden h
  | extn M x L => exact c_no_extn h
  | var _ => exact hV
  | lam _ _ => exact hV
  | app _ _ => exact hV
  | comp _ _ => exact hV
  | nm _ => exact hV

theorem envh_no_h {V N : Trm} (hV : envh V) (h : BetaH V N) : False := by
  cases V with
  | iden => exact h_no_iden h
  | extn M x L => exact h_no_extn h
  | var _ => exact hV
  | lam _ _ => exact hV
  | app _ _ => exact hV
  | comp _ _ => exact hV
  | nm _ => exact hV

theorem beta_c_det {M N1 N2 : Trm} (h1 : BetaC M N1) (h2 : BetaC M N2) : N1 = N2 := by
  induction h1 generalizing N2 with
  | Beta1 x M L N =>
    cases h2 with
    | Beta1 => rfl
    | AppL _ h' => exact (c_no_clo h').elim
  | Beta2 x M N =>
    cases h2 with
    | Beta2 => rfl
    | AppL _ h' => exact (c_no_lam h').elim
  | VarClos x y M L =>
    cases h2 with
    | VarClos => rfl
    | CompL _ h' => exact (c_no_var h').elim
    | VarR _ h' => exact (c_no_clo h').elim
  | VarLam x y M =>
    cases h2 with
    | VarLam => rfl
    | CompL _ h' => exact (c_no_var h').elim
    | VarR _ h' => exact (c_no_lam h').elim
  | AppL L h ih =>
    cases h2 with
    | Beta1 => exact (c_no_clo h).elim
    | Beta2 => exact (c_no_lam h).elim
    | AppL _ h' => rw [ih h']
  | CompL L h ih =>
    cases h2 with
    | VarClos => exact (c_no_var h).elim
    | VarLam => exact (c_no_var h).elim
    | CompL _ h' => rw [ih h']
    | VarR _ h' => exact (c_no_var h).elim
  | VarR x h ih =>
    cases h2 with
    | VarClos => exact (c_no_clo h).elim
    | VarLam => exact (c_no_lam h).elim
    | CompL _ h' => exact (c_no_var h').elim
    | VarR _ h' => rw [ih h']

theorem beta_h_imp_c_or {M N N' : Trm} (h : BetaH M N) (hc : BetaC M N') : N = N' := by
  induction h generalizing N' with
  | C h => exact beta_c_det h hc
  | AppL L h ih =>
    cases hc with
    | Beta1 => exact (h_no_clo h).elim
    | Beta2 => exact (h_no_lam h).elim
    | AppL _ h' => rw [ih h']
  | VarR x h ih =>
    cases hc with
    | VarClos => exact (h_no_clo h).elim
    | VarLam => exact (h_no_lam h).elim
    | CompL _ h' => exact (c_no_var h').elim
    | VarR _ h' => rw [ih h']
  | ArgV hV h ih =>
    cases hc with
    | Beta1 => exact hV.elim
    | Beta2 => exact hV.elim
    | AppL _ h' => exact (envh_no_c hV h').elim

theorem beta_h_det {M N1 N2 : Trm} (h1 : BetaH M N1) (h2 : BetaH M N2) : N1 = N2 := by
  induction h1 generalizing N2 with
  | C h => exact beta_h_imp_c_or h2 h |>.symm
  | AppL L h ih =>
    cases h2 with
    | C hc => exact (beta_h_imp_c_or (.AppL L h) hc)
    | AppL _ h' => rw [ih h']
    | ArgV hV _ => exact (envh_no_h hV h).elim
  | VarR x h ih =>
    cases h2 with
    | C hc => exact (beta_h_imp_c_or (.VarR x h) hc)
    | VarR _ h' => rw [ih h']
  | ArgV hV h ih =>
    cases h2 with
    | C hc => exact (beta_h_imp_c_or (.ArgV hV h) hc)
    | AppL _ h' => exact (envh_no_h hV h').elim
    | ArgV _ h' => rw [ih h']


/-! ## Congruences for σ* -/

theorem ss1 {M N : Trm} (h : Sig M N) : Star Sig M N := Star.single h

theorem ss_AppL {M N : Trm} (L : Trm) (h : Star Sig M N) : Star Sig (app M L) (app N L) :=
  Star.map (fun P => app P L) (fun _ _ h => .AppL L h) h
theorem ss_AppR {M N : Trm} (L : Trm) (h : Star Sig M N) : Star Sig (app L M) (app L N) :=
  Star.map (fun P => app L P) (fun _ _ h => .AppR L h) h
theorem ss_CompR {M N : Trm} (L : Trm) (h : Star Sig M N) : Star Sig (comp L M) (comp L N) :=
  Star.map (fun P => comp L P) (fun _ _ h => .CompR L h) h
theorem ss_CompL {M N : Trm} (L : Trm) (h : Star Sig M N) : Star Sig (comp M L) (comp N L) :=
  Star.map (fun P => comp P L) (fun _ _ h => .CompL L h) h

/-! ## Inversion of σ -/

theorem sig_nm_no {x : Var} {P : Trm} (h : Sig (nm x) P) : False := by cases h
theorem sig_var_no {x : Var} {P : Trm} (h : Sig (var x) P) : False := by cases h
theorem sig_iden_no {P : Trm} (h : Sig iden P) : False := by cases h

theorem Lam_sig_inv {x : Var} {B P : Trm} (h : Sig (lam x B) P) :
    ∃ B', P = lam x B' ∧ Sig B B' := by
  cases h with
  | Lam _ h' => exact ⟨_, rfl, h'⟩

theorem Clo_sig_inv {x : Var} {B K P : Trm} (h : Sig (comp (lam x B) K) P) :
    (∃ B', P = comp (lam x B') K ∧ Sig B B') ∨ (∃ K', P = comp (lam x B) K' ∧ Sig K K') ∨
      (K = iden ∧ P = lam x B) := by
  cases h with
  | CompL _ h' =>
    obtain ⟨B', e, h2⟩ := Lam_sig_inv h'
    exact Or.inl ⟨B', by rw [e], h2⟩
  | CompR _ h' => exact Or.inr (Or.inl ⟨_, rfl, h'⟩)
  | IdR => exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem envh_sig {V V' : Trm} (hV : envh V) (h : Sig V V') : envh V' := by
  cases V with
  | iden => exact (sig_iden_no h).elim
  | extn M x L =>
    cases h with
    | ExtnL _ _ _ => trivial
    | ExtnR _ _ _ => trivial
  | var _ => exact hV.elim
  | lam _ _ => exact hV.elim
  | app _ _ => exact hV.elim
  | comp _ _ => exact hV.elim
  | nm _ => exact hV.elim

/-! ## Commutation of a σ-step with the β-step -/

def comm_c (M1 M2 : Trm) : Prop := ∃ M1' M3, Star Sig M1 M1' ∧ BetaC M1' M3 ∧ Star Sig M2 M3

def comm (M1 M2 : Trm) : Prop := ∃ M1' M3, Star Sig M1 M1' ∧ BetaH M1' M3 ∧ Star Sig M2 M3

theorem comm_cI {M1 M1' M3 M2 : Trm} (h1 : Star Sig M1 M1') (h2 : BetaC M1' M3)
    (h3 : Star Sig M2 M3) : comm_c M1 M2 := ⟨M1', M3, h1, h2, h3⟩

theorem comm_c_direct {M1 M3 M2 : Trm} (h1 : BetaC M1 M3) (h2 : Star Sig M2 M3) :
    comm_c M1 M2 := ⟨M1, M3, .refl _, h1, h2⟩

theorem commI {M1 M1' M3 M2 : Trm} (h1 : Star Sig M1 M1') (h2 : BetaH M1' M3)
    (h3 : Star Sig M2 M3) : comm M1 M2 := ⟨M1', M3, h1, h2, h3⟩

theorem comm_direct {M1 M3 M2 : Trm} (h1 : BetaH M1 M3) (h2 : Star Sig M2 M3) : comm M1 M2 :=
  ⟨M1, M3, .refl _, h1, h2⟩

theorem comm_c_comm {M1 M2 : Trm} (h : comm_c M1 M2) : comm M1 M2 := by
  obtain ⟨a, b, h1, h2, h3⟩ := h
  exact ⟨a, b, h1, .C h2, h3⟩

/-- Pushing an environment through `P ∘ (⌜x⌝/y · K)`. -/
theorem push_name_env (P : Trm) (x y : Var) (K L : Trm) :
    Star Sig (comp (comp P (extn (nm x) y K)) L) (comp P (extn (nm x) y (comp K L))) :=
  .step (.Ass _ _ _) (.step (.CompR _ (.DExtn _ _ _ _))
    (.single (.CompR _ (.ExtnL _ _ (.ConstComp _ _)))))

theorem push_name_env_id (P : Trm) (x y : Var) (L : Trm) :
    Star Sig (comp (comp P (extn (nm x) y iden)) L) (comp P (extn (nm x) y L)) :=
  (push_name_env P x y iden L).tail (.CompR _ (.ExtnR _ _ (.IdL _)))

/-- σ* from `(B ∘ (Q/x · K)) ∘ L` to `B ∘ (Q∘L / x · K∘L)`. -/
theorem push_env (B Q : Trm) (x : Var) (K L : Trm) :
    Star Sig (comp (comp B (extn Q x K)) L) (comp B (extn (comp Q L) x (comp K L))) :=
  .step (.Ass _ _ _) (.single (.CompR _ (.DExtn _ _ _ _)))

theorem push_env_id (B Q : Trm) (x : Var) (L : Trm) :
    Star Sig (comp (comp B (extn Q x iden)) L) (comp B (extn (comp Q L) x L)) :=
  (push_env B Q x iden L).tail (.CompR _ (.ExtnR _ _ (.IdL _)))

/-! ### Case lemmas for `beta_c_sig_commute` -/

theorem comm_c_Beta1 {x : Var} {B K N M1 : Trm} (hs : Sig (app (comp (lam x B) K) N) M1) :
    comm_c M1 (comp B (extn N x K)) := by
  cases hs with
  | AppConst _ y =>
    exact comm_c_direct (.VarClos y x B K) (.refl _)
  | AppL _ hP =>
    rcases Clo_sig_inv hP with ⟨B', rfl, h1⟩ | ⟨K', rfl, h1⟩ | ⟨rfl, rfl⟩
    · exact comm_c_direct (.Beta1 x B' K N) (ss1 (.CompL _ h1))
    · exact comm_c_direct (.Beta1 x B K' N) (ss1 (.CompR _ (.ExtnR _ _ h1)))
    · exact comm_c_direct (.Beta2 x B N) (.refl _)
  | AppR _ h1 =>
    exact comm_c_direct (.Beta1 x B K _) (ss1 (.CompR _ (.ExtnL _ _ h1)))

theorem comm_c_Beta2 {x : Var} {B N M1 : Trm} (hs : Sig (app (lam x B) N) M1) :
    comm_c M1 (comp B (extn N x iden)) := by
  cases hs with
  | AppConst _ y =>
    exact comm_c_direct (.VarLam y x B) (.refl _)
  | AppL _ hP =>
    obtain ⟨B', rfl, h1⟩ := Lam_sig_inv hP
    exact comm_c_direct (.Beta2 x B' N) (ss1 (.CompL _ h1))
  | AppR _ h1 =>
    exact comm_c_direct (.Beta2 x B _) (ss1 (.CompR _ (.ExtnL _ _ h1)))

theorem comm_c_VarClos {x y : Var} {B K M1 : Trm} (hs : Sig (comp (var x) (comp (lam y B) K)) M1) :
    comm_c M1 (comp B (extn (nm x) y K)) := by
  cases hs with
  | CompL _ h' => exact (sig_var_no h').elim
  | CompR _ hP =>
    rcases Clo_sig_inv hP with ⟨B', rfl, h1⟩ | ⟨K', rfl, h1⟩ | ⟨rfl, rfl⟩
    · exact comm_c_direct (.VarClos x y B' K) (ss1 (.CompL _ h1))
    · exact comm_c_direct (.VarClos x y B K') (ss1 (.CompR _ (.ExtnR _ _ h1)))
    · exact comm_c_direct (.VarLam x y B) (.refl _)

theorem comm_c_VarLam {x y : Var} {B M1 : Trm} (hs : Sig (comp (var x) (lam y B)) M1) :
    comm_c M1 (comp B (extn (nm x) y iden)) := by
  cases hs with
  | CompL _ h' => exact (sig_var_no h').elim
  | CompR _ hP =>
    obtain ⟨B', rfl, h1⟩ := Lam_sig_inv hP
    exact comm_c_direct (.VarLam x y B') (ss1 (.CompL _ h1))

/-- The `DApp` case of `CompL`: `(App P Q) ∘ L` with `App P Q →c M'`. -/
theorem comm_c_DApp {P Q L M' : Trm} (h : BetaC (app P Q) M') :
    comm_c (app (comp P L) (comp Q L)) (comp M' L) := by
  cases h with
  | Beta1 x B K =>
    exact comm_cI (ss1 (.AppL _ (.Ass _ _ _))) (.Beta1 _ _ _ _) (push_env B Q x K L)
  | Beta2 x B =>
    exact comm_c_direct (.Beta1 _ _ _ _) (push_env_id B Q x L)
  | AppL _ h' =>
    exact comm_c_direct (.AppL _ (.CompL _ h')) (ss1 (.DApp _ _ _))

/-- The `Ass` case of `CompL`. -/
theorem comm_c_Ass {Ma Mb L M' : Trm} (h : BetaC (comp Ma Mb) M') :
    comm_c (comp Ma (comp Mb L)) (comp M' L) := by
  cases h with
  | VarClos x y P K =>
    exact comm_cI (ss1 (.CompR _ (.Ass _ _ _))) (.VarClos _ _ _ _) (push_name_env P x y K L)
  | VarLam x y P =>
    exact comm_c_direct (.VarClos _ _ _ _) (push_name_env_id P x y L)
  | CompL _ h' =>
    exact comm_c_direct (.CompL _ h') (ss1 (.Ass _ _ _))
  | VarR x h' =>
    exact comm_c_direct (.VarR x (.CompL _ h')) (ss1 (.Ass _ _ _))

theorem beta_c_sig_commute {M M2 : Trm} (hb : BetaC M M2) :
    ∀ {M1 : Trm}, Sig M M1 → comm_c M1 M2 := by
  induction hb with
  | Beta1 x B K N => intro M1 hs; exact comm_c_Beta1 hs
  | Beta2 x B N => intro M1 hs; exact comm_c_Beta2 hs
  | VarClos x y B K => intro M1 hs; exact comm_c_VarClos hs
  | VarLam x y B => intro M1 hs; exact comm_c_VarLam hs
  | AppL L h ih =>
    rename_i M M'
    intro M1 hs
    cases hs with
    | AppConst _ y =>
      exact comm_c_direct (.VarR y h) (ss1 (.AppConst _ _))
    | AppL _ hP =>
      obtain ⟨M1', M3, a1, a2, a3⟩ := ih hP
      exact comm_cI (ss_AppL L a1) (.AppL L a2) (ss_AppL L a3)
    | AppR _ h1 => exact comm_c_direct (.AppL _ h) (ss1 (.AppR _ h1))
  | CompL L h ih =>
    rename_i M M'
    intro M1 hs
    cases hs with
    | Ass Ma Mb => exact comm_c_Ass h
    | IdL => exact (c_no_iden h).elim
    | IdR => exact comm_c_direct h (ss1 (.IdR _))
    | DExtn => exact (c_no_extn h).elim
    | VarRef => exact (c_no_var h).elim
    | VarSkip => exact (c_no_var h).elim
    | DApp P Q => exact comm_c_DApp h
    | ConstComp => exact (c_no_nm h).elim
    | CompL _ hP =>
      obtain ⟨M1', M3, a1, a2, a3⟩ := ih hP
      exact comm_cI (ss_CompL L a1) (.CompL L a2) (ss_CompL L a3)
    | CompR _ h1 => exact comm_c_direct (.CompL _ h) (ss1 (.CompR _ h1))
  | VarR x h ih =>
    rename_i M M'
    intro M1 hs
    cases hs with
    | CompL _ h' => exact (sig_var_no h').elim
    | CompR _ hP =>
      obtain ⟨M1', M3, a1, a2, a3⟩ := ih hP
      exact comm_cI (ss_CompR _ a1) (.VarR x a2) (ss_CompR _ a3)
    | IdR => exact (c_no_iden h).elim
    | VarRef => exact (c_no_extn h).elim
    | VarSkip => exact (c_no_extn h).elim

theorem beta_h_sig_commute {M M2 : Trm} (hb : BetaH M M2) :
    ∀ {M1 : Trm}, Sig M M1 → comm M1 M2 := by
  induction hb with
  | C h => intro M1 hs; exact comm_c_comm (beta_c_sig_commute h hs)
  | AppL L h ih =>
    rename_i M M'
    intro M1 hs
    cases hs with
    | AppConst _ y =>
      exact comm_direct (.VarR y h) (ss1 (.AppConst _ _))
    | AppL _ hP =>
      obtain ⟨M1', M3, a1, a2, a3⟩ := ih hP
      exact commI (ss_AppL L a1) (.AppL L a2) (ss_AppL L a3)
    | AppR _ h1 => exact comm_direct (.AppL _ h) (ss1 (.AppR _ h1))
  | VarR x h ih =>
    rename_i M M'
    intro M1 hs
    cases hs with
    | CompL _ h' => exact (sig_var_no h').elim
    | CompR _ hP =>
      obtain ⟨M1', M3, a1, a2, a3⟩ := ih hP
      exact commI (ss_CompR _ a1) (.VarR x a2) (ss_CompR _ a3)
    | IdR => exact (h_no_iden h).elim
    | VarRef => exact (h_no_extn h).elim
    | VarSkip => exact (h_no_extn h).elim
  | ArgV hV h ih =>
    rename_i V M M'
    intro M1 hs
    cases hs with
    | AppConst _ y => exact (h_no_nm h).elim
    | AppL _ hP =>
      exact comm_direct (.ArgV (envh_sig hV hP) h) (ss1 (.AppL _ hP))
    | AppR _ hP =>
      obtain ⟨M1', M3, a1, a2, a3⟩ := ih hP
      exact commI (ss_AppR _ a1) (.ArgV hV a2) (ss_AppR _ a3)

/-! ## σ-normal forms -/

theorem sig_nf (M : Trm) : ∃ N, Star Sig M N ∧ sig_normal N := by
  refine SN_at.induct (P := fun M => ∃ N, Star Sig M N ∧ sig_normal N) (sig_SN M) fun a _ ih => ?_
  by_cases hn : sig_normal a
  · exact ⟨a, .refl _, hn⟩
  · have : ∃ b, Sig a b := Classical.byContradiction fun hc =>
      hn fun b hb => hc ⟨b, hb⟩
    obtain ⟨b, hb⟩ := this
    obtain ⟨N, r, n⟩ := ih b hb
    exact ⟨N, .step hb r, n⟩

theorem sig_steps_tlength {M N : Trm} (h : Star Sig M N) : tlength N ≤ tlength M := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h _ ih => have := sig_tlength_decrease h; omega

noncomputable def snf (M : Trm) : Trm := Classical.choose (sig_nf M)

theorem snf_spec (M : Trm) : Star Sig M (snf M) ∧ sig_normal (snf M) :=
  Classical.choose_spec (sig_nf M)

theorem snf_unique {M N : Trm} (r : Star Sig M N) (n : sig_normal N) : snf M = N := by
  obtain ⟨P, p1, p2⟩ := sig_confluent (snf_spec M).1 r
  have e1 := normal_star (snf_spec M).2 p1
  have e2 := normal_star n p2
  rw [← e1, e2]

theorem snf_steps {M M' : Trm} (r : Star Sig M M') : snf M' = snf M := by
  have h : Star Sig M (snf M') := r.trans (snf_spec M').1
  exact (snf_unique h (snf_spec M').2).symm

theorem snf_beta {M M' : Trm} (hb : BetaH M M') : ∃ M3, BetaH (snf M) M3 ∧ Star Sig M' M3 := by
  have key : ∀ k (M M' : Trm), tlength M ≤ k → BetaH M M' →
      ∃ M3, BetaH (snf M) M3 ∧ Star Sig M' M3 := by
    intro k
    induction k with
    | zero => intro M _ hk; have := tlength_pos M; omega
    | succ k ih =>
      intro M M' hk hb
      by_cases hn : ∃ M1, Sig M M1
      · obtain ⟨M1, s⟩ := hn
        obtain ⟨M1', M3', a1, a2, a3⟩ := beta_h_sig_commute hb s
        have lt : tlength M1' < tlength M := by
          have := sig_tlength_decrease s
          have := sig_steps_tlength a1
          omega
        obtain ⟨M3, b1, b2⟩ := ih M1' M3' (by omega) a2
        have e : snf M1' = snf M := snf_steps (.step s a1)
        rw [e] at b1
        exact ⟨M3, b1, a3.trans b2⟩
      · have e : snf M = M := snf_unique (.refl _) (fun b h => hn ⟨b, h⟩)
        rw [e]
        exact ⟨M', hb, .refl _⟩
  exact key _ M M' (Nat.le_refl _) hb

/-! ## The deterministic chain -/

inductive cd : Trm → Nat → Trm → Prop where
  | cd0 {M : Trm} : normal BetaH (snf M) → cd M 0 (snf M)
  | cdS {M N : Trm} {n : Nat} {E : Trm} : BetaH (snf M) N → cd N n E → cd M (n + 1) E

theorem cd_snf {A B : Trm} {n : Nat} {E : Trm} (h : cd A n E) (e : snf A = snf B) : cd B n E := by
  cases h with
  | cd0 hn => rw [e] at hn ⊢; exact .cd0 hn
  | cdS h1 h2 => rw [e] at h1; exact .cdS h1 h2

theorem cd_det {M : Trm} {n : Nat} {E : Trm} (h : cd M n E) :
    ∀ {n' : Nat} {E' : Trm}, cd M n' E' → n = n' ∧ E = E' := by
  induction h with
  | cd0 hn =>
    intro n' E' h2
    cases h2 with
    | cd0 => exact ⟨rfl, rfl⟩
    | cdS h1 _ => exact (hn _ h1).elim
  | cdS h ih ih2 =>
    intro n' E' h2
    cases h2 with
    | cd0 hn => exact (hn _ h).elim
    | cdS h1 c' =>
      have := beta_h_det h h1
      subst this
      obtain ⟨a, b⟩ := ih2 c'
      exact ⟨by rw [a], b⟩

theorem cd_back_sig {M M' : Trm} {n : Nat} {E : Trm} (h : Sig M M') (c : cd M' n E) : cd M n E :=
  cd_snf c (snf_steps (ss1 h))

theorem cd_fwd_sig {M M' : Trm} {n : Nat} {E : Trm} (h : Sig M M') (c : cd M n E) : cd M' n E :=
  cd_snf c (snf_steps (ss1 h)).symm

theorem cd_back_beta {M M' : Trm} {n : Nat} {E : Trm} (b : BetaH M M') (c : cd M' n E) :
    cd M (n + 1) E := by
  obtain ⟨M3, m1, m2⟩ := snf_beta b
  have : cd M3 n E := cd_snf c (snf_steps m2).symm
  exact .cdS m1 this

theorem cd_fwd_beta {M M' : Trm} {n : Nat} {E : Trm} (b : BetaH M M') (c : cd M n E) :
    ∃ m, n = m + 1 ∧ cd M' m E := by
  obtain ⟨M3, m1, m2⟩ := snf_beta b
  cases c with
  | cd0 hn => exact (hn _ m1).elim
  | cdS h1 h2 =>
    have e := beta_h_det h1 m1
    subst e
    exact ⟨_, rfl, cd_snf h2 (snf_steps m2)⟩

theorem WHNF_cd {N : Trm} (n : WHNF N) : cd N 0 N := by
  have sn : snf N = N := snf_unique (.refl _) (WHNF_imp_sig_normal n)
  have hn : normal BetaH N := fun b h => n b (Or.inr h)
  have := cd.cd0 (M := N) (by rw [sn]; exact hn)
  rwa [sn] at this

theorem steps_cd {M N : Trm} (r : WhSteps M N) (n : WHNF N) : ∃ k, cd M k N := by
  induction r with
  | refl => exact ⟨0, WHNF_cd n⟩
  | step h _ ih =>
    obtain ⟨k, c⟩ := ih n
    rcases h with h | h
    · exact ⟨k, cd_back_sig h c⟩
    · exact ⟨k + 1, cd_back_beta h c⟩

theorem cd_WHSN {M : Trm} {n : Nat} {E : Trm} (h : cd M n E) : WHSN M := by
  induction n using Nat.strongRecOn generalizing M with
  | _ n IHn =>
    have key : ∀ k (M : Trm), tlength M ≤ k → cd M n E → WHSN M := by
      intro k
      induction k with
      | zero => intro M hk; have := tlength_pos M; omega
      | succ k ihk =>
        intro M hk c
        refine SN_at.intro fun N s => ?_
        rcases s with s | s
        · exact ihk N (by have := sig_tlength_decrease s; omega) (cd_fwd_sig s c)
        · obtain ⟨m, hm, c'⟩ := cd_fwd_beta s c
          exact IHn m (by omega) c'
    exact key _ M (Nat.le_refl _) h

theorem cd_reach_end {M N' : Trm} (r : WhSteps M N') {n : Nat} {E : Trm} (c : cd M n E)
    (w : WHNF N') : N' = E := by
  induction r generalizing n with
  | refl => exact (cd_det (WHNF_cd w) c).2
  | step h _ ih =>
    rcases h with h | h
    · exact ih (cd_fwd_sig h c) w
    · obtain ⟨m, _, c'⟩ := cd_fwd_beta h c
      exact ih c' w

theorem CFWHN_imp_CFWHSN {M : Trm} (h : CFWHN M) : CFWHSN M := by
  obtain ⟨N, r, n, c⟩ := h
  obtain ⟨k, cdM⟩ := steps_cd r n
  refine ⟨cd_WHSN cdM, fun N' r' n' hc => ?_⟩
  have := cd_reach_end r' cdM n'
  subst this
  exact c hc

theorem WHNF_unique {M N1 N2 : Trm} (r1 : WhSteps M N1) (n1 : WHNF N1)
    (r2 : WhSteps M N2) (n2 : WHNF N2) : N1 = N2 := by
  obtain ⟨k, c⟩ := steps_cd r1 n1
  exact (cd_reach_end r2 c n2).symm

theorem WHSN_reaches_WHNF {M : Trm} (h : WHSN M) : ∃ N, WhSteps M N ∧ WHNF N := by
  refine SN_at.induct (P := fun M => ∃ N, WhSteps M N ∧ WHNF N) h fun a _ ih => ?_
  by_cases hn : WHNF a
  · exact ⟨a, .refl _, hn⟩
  · have : ∃ b, Wh a b := Classical.byContradiction fun hc =>
      hn fun b hb => hc ⟨b, hb⟩
    obtain ⟨b, hb⟩ := this
    obtain ⟨N, r, n⟩ := ih b hb
    exact ⟨N, .step hb r, n⟩

theorem CFWHSN_imp_CFWHN {M : Trm} (h : CFWHSN M) : CFWHN M := by
  obtain ⟨N, r, n⟩ := WHSN_reaches_WHNF h.1
  exact ⟨N, r, n, h.2 N r n⟩

theorem CFWHN_fwd {M M' : Trm} (s : Wh M M') (h : CFWHN M) : CFWHN M' := by
  have h' := CFWHN_imp_CFWHSN h
  apply CFWHSN_imp_CFWHN
  exact ⟨h'.1.step s, fun N r n => h'.2 N (.step s r) n⟩

theorem Nm_WHNF (x : Var) : WHNF (nm x) := by
  intro b h
  rcases h with h | h
  · exact sig_nm_no h
  · exact h_no_nm h

theorem Nm_fwd {M M' : Trm} {x : Var} (s : Wh M M') (h : WhSteps M (nm x)) :
    WhSteps M' (nm x) := by
  obtain ⟨k, c⟩ := steps_cd h (Nm_WHNF x)
  obtain ⟨N, r', n⟩ := WHSN_reaches_WHNF ((cd_WHSN c).step s)
  have e : N = nm x := WHNF_unique (.step s r') n h (Nm_WHNF x)
  rw [e] at r'
  exact r'

end LambdaPEnvWH
