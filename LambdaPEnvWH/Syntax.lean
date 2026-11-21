/-!
# Syntax of λpenv_wh: λenv with quoted names

Port of `Syntax.thy`.  Term variables are natural numbers.  There is no
α-equivalence: equality of terms is syntactic identity of the first-order datatype.
-/

namespace LambdaPEnvWH

abbrev Var := Nat

inductive Trm where
  | var (x : Var)
  | lam (x : Var) (M : Trm)
  | app (M N : Trm)
  | iden
  | extn (M : Trm) (x : Var) (N : Trm)
  | comp (M N : Trm)
  /-- quoted name `⌜x⌝` -/
  | nm (x : Var)
  deriving DecidableEq, Repr, Inhabited

open Trm

/-- The polynomial measure used for termination of σ. -/
def tlength : Trm → Nat
  | var _ => 1
  | app M N => tlength M + tlength N + 1
  | lam _ M => tlength M * 2
  | comp M N => tlength M * (tlength N + 1)
  | iden => 1
  | extn M _ N => tlength M + tlength N + 1
  | nm _ => 1

theorem tlength_pos (M : Trm) : 0 < tlength M := by
  induction M with
  | var => simp [tlength]
  | lam _ M ih => simp only [tlength]; omega
  | app M N ihM ihN => simp only [tlength]; omega
  | iden => simp [tlength]
  | extn M _ N ihM ihN => simp only [tlength]; omega
  | comp M N ihM ihN => simp only [tlength]; exact Nat.mul_pos ihM (Nat.succ_pos _)
  | nm => simp [tlength]

/-- The variables occurring in a term (a finite list). -/
def names : Trm → List Var
  | var x => [x]
  | lam x M => x :: names M
  | app M N => names M ++ names N
  | iden => []
  | extn M x N => x :: (names M ++ names N)
  | comp M N => names M ++ names N
  | nm x => [x]

/-- Environment heads: `id` and extensions. -/
def envh : Trm → Prop
  | iden => True
  | extn _ _ _ => True
  | _ => False

end LambdaPEnvWH
