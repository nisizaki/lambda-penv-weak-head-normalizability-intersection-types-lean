import LambdaPEnvWH.Sorted
import LambdaPEnvWH.Main_Results

/-!
# Conservativity over λenv on sorted terms

Port of `Conservative.thy`.
-/

namespace LambdaPEnvWH

theorem envh_not_tm {V : Trm} (h : envh V) : ¬ tm V := by
  cases V <;> simp [envh, tm] at *

theorem sig0_imp_sig {M N : Trm} (h : Sig0 M N) : Sig M N := by
  induction h with
  | Ass L M N => exact .Ass L M N
  | IdL M => exact .IdL M
  | IdR M => exact .IdR M
  | DExtn L x M N => exact .DExtn L x M N
  | VarRef x M N => exact .VarRef x M N
  | VarSkip M N h => exact .VarSkip M N h
  | DApp M1 M2 N => exact .DApp M1 M2 N
  | AppL L _ ih => exact .AppL L ih
  | AppR L _ ih => exact .AppR L ih
  | Lam x _ ih => exact .Lam x ih
  | CompL L _ ih => exact .CompL L ih
  | CompR L _ ih => exact .CompR L ih
  | ExtnL x L _ ih => exact .ExtnL x L ih
  | ExtnR L x _ ih => exact .ExtnR L x ih

theorem sig_sorted_imp_sig0 {M N : Trm} (h : Sig M N) : tm M ∨ en M → Sig0 M N := by
  induction h with
  | Ass L M N => intro _; exact .Ass L M N
  | IdL M => intro _; exact .IdL M
  | IdR M => intro _; exact .IdR M
  | DExtn L x M N => intro _; exact .DExtn L x M N
  | VarRef x M N => intro _; exact .VarRef x M N
  | VarSkip M N h => intro _; exact .VarSkip M N h
  | DApp M1 M2 N => intro _; exact .DApp M1 M2 N
  | AppConst M x => intro hs; simp [tm, en] at hs
  | ConstComp x L => intro hs; simp [tm, en] at hs
  | AppL L _ ih => intro hs; simp [tm, en] at hs; exact .AppL L (ih (.inl hs.1))
  | AppR L _ ih => intro hs; simp [tm, en] at hs; exact .AppR L (ih (.inl hs.2))
  | Lam x _ ih => intro hs; simp [tm, en] at hs; exact .Lam x (ih (.inl hs))
  | CompL L _ ih =>
    intro hs; simp only [tm, en] at hs
    rcases hs with hs | hs
    · exact .CompL L (ih (.inl hs.1))
    · exact .CompL L (ih (.inr hs.1))
  | CompR L _ ih =>
    intro hs; simp only [tm, en] at hs
    rcases hs with hs | hs
    · exact .CompR L (ih (.inr hs.2))
    · exact .CompR L (ih (.inr hs.2))
  | ExtnL x L _ ih => intro hs; simp [tm, en] at hs; exact .ExtnL x L (ih (.inl hs.1))
  | ExtnR L x _ ih => intro hs; simp [tm, en] at hs; exact .ExtnR L x (ih (.inr hs.2))

theorem sorted_sig_iff {M N : Trm} (h : tm M ∨ en M) : Sig M N ↔ Sig0 M N :=
  ⟨fun hs => sig_sorted_imp_sig0 hs h, sig0_imp_sig⟩

theorem beta0_imp_betaC {M N : Trm} (h : Beta0 M N) : BetaC M N := by
  induction h with
  | Beta1 x M L N => exact .Beta1 x M L N
  | Beta2 x M N => exact .Beta2 x M N
  | AppL L _ ih => exact .AppL L ih
  | CompL L _ ih => exact .CompL L ih
  | VarR x _ ih => exact .VarR x ih

theorem betaC_imp_betaH {M N : Trm} (h : BetaC M N) : BetaH M N := .C h

theorem betaC_sorted_imp_beta0 {M N : Trm} (h : BetaC M N) : tm M ∨ en M → Beta0 M N := by
  induction h with
  | Beta1 x M L N => intro _; exact .Beta1 x M L N
  | Beta2 x M N => intro _; exact .Beta2 x M N
  | VarClos x y M L => intro hs; simp [tm, en] at hs
  | VarLam x y M => intro hs; simp [tm, en] at hs
  | AppL L _ ih => intro hs; simp [tm, en] at hs; exact .AppL L (ih (.inl hs.1))
  | CompL L _ ih =>
    intro hs; simp only [tm, en] at hs
    rcases hs with hs | hs
    · exact .CompL L (ih (.inl hs.1))
    · exact .CompL L (ih (.inr hs.1))
  | VarR x _ ih =>
    intro hs; simp only [tm, en] at hs
    rcases hs with hs | hs
    · exact .VarR x (ih (.inr hs.2))
    · exact absurd hs.1 (by simp [en])

theorem betaH_sorted_imp_beta0 {M N : Trm} (h : BetaH M N) : tm M ∨ en M → Beta0 M N := by
  induction h with
  | C h => exact betaC_sorted_imp_beta0 h
  | AppL L _ ih => intro hs; simp [tm, en] at hs; exact .AppL L (ih (.inl hs.1))
  | VarR x _ ih =>
    intro hs; simp only [tm, en] at hs
    rcases hs with hs | hs
    · exact .VarR x (ih (.inr hs.2))
    · exact absurd hs.1 (by simp [en])
  | ArgV hV _ _ =>
    intro hs
    rcases hs with hs | hs
    · exact absurd hs.1 (envh_not_tm hV)
    · simp [en] at hs

theorem sorted_beta_iff {M N : Trm} (h : tm M ∨ en M) : BetaH M N ↔ Beta0 M N :=
  ⟨fun hs => betaH_sorted_imp_beta0 hs h, fun hb => betaC_imp_betaH (beta0_imp_betaC hb)⟩

theorem sorted_wh_iff {M N : Trm} (h : tm M ∨ en M) : Wh M N ↔ Wh0 M N := by
  unfold Wh Wh0
  rw [sorted_sig_iff h, sorted_beta_iff h]

theorem sig0_sorted {M N : Trm} (h : Sig0 M N) : (tm M → tm N) ∧ (en M → en N) := by
  induction h with
  | Ass L M N => simp only [tm, en]; grind
  | IdL M => simp only [tm, en]; grind
  | IdR M => simp only [tm, en]; grind
  | DExtn L x M N => simp only [tm, en]; grind
  | VarRef x M N => simp only [tm, en]; grind
  | VarSkip M N _ => simp only [tm, en]; grind
  | DApp M1 M2 N => simp only [tm, en]; grind
  | AppL L _ ih => simp only [tm, en]; grind
  | AppR L _ ih => simp only [tm, en]; grind
  | Lam x _ ih => simp only [tm, en]; grind
  | CompL L _ ih => simp only [tm, en]; grind
  | CompR L _ ih => simp only [tm, en]; grind
  | ExtnL x L _ ih => simp only [tm, en]; grind
  | ExtnR L x _ ih => simp only [tm, en]; grind

theorem beta0_sorted {M N : Trm} (h : Beta0 M N) : (tm M → tm N) ∧ (en M → en N) := by
  induction h with
  | Beta1 x M L N => simp only [tm, en]; grind
  | Beta2 x M N => simp only [tm, en]; grind
  | AppL L _ ih => simp only [tm, en]; grind
  | CompL L _ ih => simp only [tm, en]; grind
  | VarR x _ ih => simp only [tm, en]; grind

theorem wh_sorted {M N : Trm} (h : Wh M N) : (tm M → tm N) ∧ (en M → en N) := by
  constructor
  · intro t
    have h0 := (sorted_wh_iff (.inl t)).1 h
    rcases h0 with h0 | h0
    · exact (sig0_sorted h0).1 t
    · exact (beta0_sorted h0).1 t
  · intro t
    have h0 := (sorted_wh_iff (.inr t)).1 h
    rcases h0 with h0 | h0
    · exact (sig0_sorted h0).2 t
    · exact (beta0_sorted h0).2 t

theorem wh_steps_sorted {M N : Trm} (r : WhSteps M N) (t : tm M) : tm N := by
  induction r with
  | refl => exact t
  | step h _ ih => exact ih ((wh_sorted h).1 t)

theorem sorted_not_clash' {M : Trm} (h : clash M) : ¬ (tm M ∨ en M) := by
  induction h with
  | CNmApp x _ _ => simp [tm, en]
  | CEnv hV _ _ _ =>
    rename_i V W
    intro hs
    rcases hs with hs | hs
    · exact envh_not_tm hV hs.1
    · simp [en] at hs
  | CApp _ _ _ ih => simp only [tm, en]; grind
  | CVarNm x y => simp [tm, en]
  | CComp x _ ih => simp only [tm, en]; grind

theorem sorted_not_clash {M : Trm} (t : tm M) : ¬ clash M :=
  fun h => sorted_not_clash' h (.inl t)

theorem sorted_wh_steps_iff {M N : Trm} (t : tm M) : WhSteps M N ↔ Star Wh0 M N := by
  constructor
  · intro r
    induction r with
    | refl => exact .refl _
    | step h _ ih =>
      exact .step ((sorted_wh_iff (.inl t)).1 h) (ih ((wh_sorted h).1 t))
  · intro r
    induction r with
    | refl => exact .refl _
    | step h _ ih =>
      exact .step ((sorted_wh_iff (.inl t)).2 h) (ih ((wh_sorted ((sorted_wh_iff (.inl t)).2 h)).1 t))

theorem sorted_normal_iff {N : Trm} (t : tm N) : normal Wh N ↔ normal Wh0 N := by
  constructor
  · intro h b hb
    exact h b ((sorted_wh_iff (.inl t)).2 hb)
  · intro h b hb
    exact h b ((sorted_wh_iff (.inl t)).1 hb)

theorem conservative_CFWHN {M : Trm} (t : tm M) : CFWHN M ↔ CFWHN0 M := by
  constructor
  · rintro ⟨N, r, n, _⟩
    have tN := wh_steps_sorted r t
    exact ⟨N, (sorted_wh_steps_iff t).1 r, (sorted_normal_iff tN).1 n⟩
  · rintro ⟨N, r, n⟩
    have r' := (sorted_wh_steps_iff t).2 r
    have tN := wh_steps_sorted r' t
    exact ⟨N, r', (sorted_normal_iff tN).2 n, sorted_not_clash tN⟩

theorem conservative_Typ {M : Trm} (t : tm M) : Typ M ↔ CFWHN0 M :=
  main_characterization.trans (conservative_CFWHN t)

end LambdaPEnvWH
