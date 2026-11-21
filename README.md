# Weak-Head Normalizability of λpenv and its Characterization by Intersection Types (Lean 4)

This repository contains the Lean 4 formalization accompanying the paper

> Shin-ya Nishizaki and Shogo Murasaki.
> *Mixing Functions and Environments: Weak-Head Normalizability of λpenv and its
> Characterization by Intersection Types, Formalized in Isabelle/HOL.*

The paper's primary formalization is in Isabelle/HOL
(<https://github.com/nisizaki/lambda-penv-weak-head-normalizability-intersection-types>).
This repository ports that development to Lean 4, with one Lean file per Isabelle
theory and the same definitions and theorem names.

λpenv extends the calculus λenv of first-class environments with quoted names `⌜x⌝`
(constructor `nm x`), so that functions and environments can be used interchangeably.

## Main results

```lean
theorem main_characterization    : Typ M ↔ CFWHN M
theorem main_characterization_SN : Typ M ↔ CFWHSN M
theorem clash_not_Typ            : WHNF M → clash M → ¬ Typ M
theorem WHNF_unique              : WhSteps M N1 → WHNF N1 → WhSteps M N2 → WHNF N2 → N1 = N2
theorem sorted_wh_iff            : tm M ∨ en M → (Wh M N ↔ Wh0 M N)
theorem conservative_Typ         : tm M → (Typ M ↔ CFWHN0 M)
theorem E1                       : pure M → (lam_WHN (rb M DVar) ↔ CFWHN M) ∧ (CFWHN M ↔ CFWHSN M)
theorem pure_characterization    : pure M → (Typ M ↔ lam_WHN (rb M DVar))
```

All 15 Isabelle theories are ported, one Lean file each with the same name.

- There is no `sorry`, `axiom` or `native_decide`.
- `#print axioms` for the main theorems reports only `propext`, `Classical.choice` and
  `Quot.sound`.
- `autoImplicit` is disabled.

## Adaptations

- Sets of terms become predicates, and `rtranclp` becomes `Star`.
- Constructor and type names:
  - `Id`, `Extn`, `Comp`, `Nm` become `iden`, `extn`, `comp`, `nm`.
  - `ty`, `sub`, `hasty` become `Ty`, `Sub` (`≼`), `Hasty` (`⊢`).
  - The head β-relations `beta_c` and `beta_h` become `BetaC` and `BetaH`.
- In `Sub`, the rule `s_env` is a theorem. The constructor `s_env_core` splits its
  existential premise; this is equivalent because `map_of` is functional.
- `qfree` (types without name types) is defined with an auxiliary function on binding
  lists.
- `snf` (the σ-normal form) uses `Classical.choose` instead of Isabelle's `SOME`.

Authors: Shin-ya Nishizaki and Shogo Murasaki.

## Building

Requires Lean 4 v4.33.1, which `elan` installs automatically from `lean-toolchain`.
There are no dependencies beyond the Lean core library (no Mathlib).

```bash
lake build
```

To list the axioms used by a theorem:

```lean
import LambdaPEnvWH
#print axioms LambdaPEnvWH.main_characterization
```

## Files

```
lean-toolchain, lakefile.toml, lake-manifest.json   Lake project (Lean v4.33.1, no dependencies)
LambdaPEnvWH.lean                                    root module importing all files
LambdaPEnvWH/*.lean                                  one file per Isabelle theory (15 files)
```

## Related repositories

- Isabelle/HOL original of this development:
  [lambda-penv-weak-head-normalizability-intersection-types](https://github.com/nisizaki/lambda-penv-weak-head-normalizability-intersection-types)
- Call-by-value λpenv:
  [lambda-penv-call-by-value-termination-intersection-types](https://github.com/nisizaki/lambda-penv-call-by-value-termination-intersection-types)
  ([Lean 4](https://github.com/nisizaki/lambda-penv-call-by-value-termination-intersection-types-lean))
- The corresponding λenv development:
  [lambda-env-weak-head-normalizability-intersection-types](https://github.com/nisizaki/lambda-env-weak-head-normalizability-intersection-types)
  ([Lean 4](https://github.com/nisizaki/lambda-env-weak-head-normalizability-intersection-types-lean))
- λpenv and the confluence of its weak reduction:
  [lambda-penv-confluence-public](https://github.com/nisizaki/lambda-penv-confluence-public)

## How to cite

Cite the paper quoted at the top of this file.
