import LambdaPEnvWH.Soundness

/-!
# Main results

Port of `Main_Results.thy` (λpenv_wh).
-/

namespace LambdaPEnvWH

theorem main_characterization {M : Trm} : Typ M ↔ CFWHN M :=
  ⟨soundness, completeness⟩

theorem main_characterization_SN {M : Trm} : Typ M ↔ CFWHSN M :=
  ⟨fun h => CFWHN_imp_CFWHSN (soundness h), fun h => completeness (CFWHSN_imp_CFWHN h)⟩

theorem clash_not_Typ {M : Trm} (n : WHNF M) (c : clash M) : ¬ Typ M := by
  intro t
  obtain ⟨N, r, _, cN⟩ := soundness t
  have : N = M := normal_star n r
  exact cN (this ▸ c)

end LambdaPEnvWH
