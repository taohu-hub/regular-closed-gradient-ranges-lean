module

public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command

@[expose] public section

/-!
Fail the check if a declaration transitively uses any axiom other than
the three standard Lean/mathlib foundations allowed in this project.
In particular, this rejects `sorryAx` and custom mathematical axioms.
It does not replace review of the declaration's hypotheses and conclusion.
-/

open Lean Elab Command

elab "assert_standard_axioms " ns:ident+ : command => do
  for n in ns do
    let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n} depends on disallowed axiom {ax}"
