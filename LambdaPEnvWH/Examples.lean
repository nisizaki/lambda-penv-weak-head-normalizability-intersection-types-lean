import LambdaPEnvWH.Main_Results

/-!
# Examples

Port of `Examples.thy`.  Variables are natural numbers: x = 0, y = 1, and so on.
Examples of reductions and typings.
-/

namespace LambdaPEnvWH

open Trm

/-! ## Helpers -/

/-- A term that weakly reduces to a non-clashing weak-head normal form is typable. -/
theorem ex_Typ_of_nf {M N : Trm} (r : WhSteps M N) (n : WHNF N) (c : ¬ clash N) : Typ M :=
  main_characterization.mpr ⟨N, r, n, c⟩

theorem ex_envh_Id : envh iden := trivial

theorem ex_notNm_var (x : Var) : notNm (var x) := by
  intro y h
  cases h

/-! ## 1. `x∘(λy.y)`, a function used as an environment -/

theorem ex1_step1 : Wh (comp (var 0) (lam 1 (var 1))) (comp (var 1) (extn (nm 0) 1 iden)) :=
  beta_h_imp_wh (.C (.VarLam 0 1 (var 1)))

theorem ex1_step2 : Wh (comp (var 1) (extn (nm 0) 1 iden)) (nm 0) :=
  sig_imp_wh (.VarRef 1 (nm 0) iden)

theorem ex1_red : WhSteps (comp (var 0) (lam 1 (var 1))) (nm 0) :=
  .step ex1_step1 (.single ex1_step2)

theorem ex1_Typ : Typ (comp (var 0) (lam 1 (var 1))) :=
  ex_Typ_of_nf ex1_red (WHNF_Nm 0) (val_not_clash (.VNm 0))

/-! ## 2. `(id/0·id)∘⌜0⌝`, an environment used as a function -/

theorem ex2_step1 : Wh (app (extn iden 0 iden) (nm 0)) (comp (var 0) (extn iden 0 iden)) :=
  sig_imp_wh (.AppConst (extn iden 0 iden) 0)

theorem ex2_step2 : Wh (comp (var 0) (extn iden 0 iden)) iden :=
  sig_imp_wh (.VarRef 0 iden iden)

theorem ex2_red : WhSteps (app (extn iden 0 iden) (nm 0)) iden :=
  .step ex2_step1 (.single ex2_step2)

theorem ex2_Typ : Typ (app (extn iden 0 iden) (nm 0)) :=
  ex_Typ_of_nf ex2_red WHNF_Id (val_not_clash .VId)

/-! ## 3. `id 1`, a clash -/

theorem ex3_clash : clash (app iden (var 1)) :=
  .CEnv ex_envh_Id (WHNF_imp_sig_normal WHNF_Id) (WHNF_Var 1) (ex_notNm_var 1)

theorem ex3_WHNF : WHNF (app iden (var 1)) := clash_WHNF ex3_clash

theorem ex3_not_Typ : ¬ Typ (app iden (var 1)) := clash_not_Typ ex3_WHNF ex3_clash

/-! ## 4. `⌜0⌝ 1` and `0∘⌜1⌝`, clashes -/

theorem ex4a_clash : clash (app (nm 0) (var 1)) :=
  .CNmApp 0 (WHNF_imp_sig_normal (WHNF_Var 1)) (ex_notNm_var 1)

theorem ex4a_WHNF : WHNF (app (nm 0) (var 1)) := clash_WHNF ex4a_clash

theorem ex4a_not_Typ : ¬ Typ (app (nm 0) (var 1)) := clash_not_Typ ex4a_WHNF ex4a_clash

theorem ex4b_clash : clash (comp (var 0) (nm 1)) := .CVarNm 0 1

theorem ex4b_WHNF : WHNF (comp (var 0) (nm 1)) := clash_WHNF ex4b_clash

theorem ex4b_not_Typ : ¬ Typ (comp (var 0) (nm 1)) := clash_not_Typ ex4b_WHNF ex4b_clash

/-! ## 5. `id((λ2.⌜0⌝) 1)`, using ArgV -/

theorem ex5_step1 :
    Wh (app iden (app (lam 2 (nm 0)) (var 1))) (app iden (comp (nm 0) (extn (var 1) 2 iden))) :=
  beta_h_imp_wh (.ArgV ex_envh_Id (.C (.Beta2 2 (nm 0) (var 1))))

theorem ex5_step2 :
    Wh (app iden (comp (nm 0) (extn (var 1) 2 iden))) (app iden (nm 0)) :=
  sig_imp_wh (.AppR iden (.ConstComp 0 (extn (var 1) 2 iden)))

theorem ex5_step3 : Wh (app iden (nm 0)) (comp (var 0) iden) :=
  sig_imp_wh (.AppConst iden 0)

theorem ex5_step4 : Wh (comp (var 0) iden) (var 0) :=
  sig_imp_wh (.IdR (var 0))

theorem ex5_red : WhSteps (app iden (app (lam 2 (nm 0)) (var 1))) (var 0) :=
  .step ex5_step1 (.step ex5_step2 (.step ex5_step3 (.single ex5_step4)))

theorem ex5_Typ : Typ (app iden (app (lam 2 (nm 0)) (var 1))) :=
  ex_Typ_of_nf ex5_red (WHNF_Var 0) (neu_not_clash (.NVar 0))

end LambdaPEnvWH
