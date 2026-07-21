/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import BasaltExamples.STLC.Syntax
import BasaltExamples.STLC.GenType
import BasaltExamples.STLC.GenTerm
import BasaltExamples.STLC.TypeCheck

/-!
# Simply-Typed Lambda Calculus

An example generator for well-typed terms of the simply-typed lambda calculus (extended with
Bools), together with a typechecker. Split across `BasaltExamples/STLC/`:

* `Syntax`    — types, terms, contexts, and the typing judgement.
* `GenType`   — `genType`, an arbitrary-type generator, with its laws.
* `GenTerm`   — `genTerm`, a well-typed-term generator, with soundness and completeness.
* `TypeCheck` — a decidable typechecker, proved sound and complete.
-/
