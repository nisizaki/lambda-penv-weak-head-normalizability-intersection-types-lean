import LambdaPEnvWH.Reduction

/-!
# Sorted terms and the λenv fragment of the reduction

Port of `Sorted.thy`.  `tm`: term-sorted, `en`: environment-sorted (as in λenv); quoted names
are neither.  `Sig0`, `Beta0`, `Wh0` are the λenv reductions, copied verbatim.
-/

namespace LambdaPEnvWH

open Trm

mutual
def tm : Trm → Prop
  | var _ => True
  | lam _ M => tm M
  | app M N => tm M ∧ tm N
  | comp M L => tm M ∧ en L
  | iden => False
  | extn _ _ _ => False
  | nm _ => False
def en : Trm → Prop
  | var _ => False
  | lam _ _ => False
  | app _ _ => False
  | comp L1 L2 => en L1 ∧ en L2
  | iden => True
  | extn M _ L => tm M ∧ en L
  | nm _ => False
end

def pure : Trm → Prop
  | var _ => True
  | lam _ M => pure M
  | app M N => pure M ∧ pure N
  | _ => False

theorem pure_tm {M : Trm} (h : pure M) : tm M := by
  induction M with
  | var => trivial
  | lam _ M ih => exact ih h
  | app M N ihM ihN => exact ⟨ihM h.1, ihN h.2⟩
  | iden => exact h.elim
  | extn => exact h.elim
  | comp => exact h.elim
  | nm => exact h.elim

inductive Sig0 : Trm → Trm → Prop where
  | Ass (L M N : Trm) : Sig0 (comp (comp L M) N) (comp L (comp M N))
  | IdL (M : Trm) : Sig0 (comp iden M) M
  | IdR (M : Trm) : Sig0 (comp M iden) M
  | DExtn (L : Trm) (x : Var) (M N : Trm) : Sig0 (comp (extn L x M) N) (extn (comp L N) x (comp M N))
  | VarRef (x : Var) (M N : Trm) : Sig0 (comp (var x) (extn M x N)) M
  | VarSkip {x y : Var} (M N : Trm) : x ≠ y → Sig0 (comp (var y) (extn M x N)) (comp (var y) N)
  | DApp (M1 M2 N : Trm) : Sig0 (comp (app M1 M2) N) (app (comp M1 N) (comp M2 N))
  | AppL {M N : Trm} (L : Trm) : Sig0 M N → Sig0 (app M L) (app N L)
  | AppR {M N : Trm} (L : Trm) : Sig0 M N → Sig0 (app L M) (app L N)
  | Lam {M N : Trm} (x : Var) : Sig0 M N → Sig0 (lam x M) (lam x N)
  | CompL {M N : Trm} (L : Trm) : Sig0 M N → Sig0 (comp M L) (comp N L)
  | CompR {M N : Trm} (L : Trm) : Sig0 M N → Sig0 (comp L M) (comp L N)
  | ExtnL {M N : Trm} (x : Var) (L : Trm) : Sig0 M N → Sig0 (extn M x L) (extn N x L)
  | ExtnR {M N : Trm} (L : Trm) (x : Var) : Sig0 M N → Sig0 (extn L x M) (extn L x N)

inductive Beta0 : Trm → Trm → Prop where
  | Beta1 (x : Var) (M L N : Trm) : Beta0 (app (comp (lam x M) L) N) (comp M (extn N x L))
  | Beta2 (x : Var) (M N : Trm) : Beta0 (app (lam x M) N) (comp M (extn N x iden))
  | AppL {M N : Trm} (L : Trm) : Beta0 M N → Beta0 (app M L) (app N L)
  | CompL {M N : Trm} (L : Trm) : Beta0 M N → Beta0 (comp M L) (comp N L)
  | VarR {M N : Trm} (x : Var) : Beta0 M N → Beta0 (comp (var x) M) (comp (var x) N)

def Wh0 (M N : Trm) : Prop := Sig0 M N ∨ Beta0 M N

def CFWHN0 (M : Trm) : Prop := ∃ N, Star Wh0 M N ∧ normal Wh0 N

end LambdaPEnvWH
