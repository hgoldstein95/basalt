/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/
import Basalt.Basic

/-!
# Basalt

This library provides comprehensive infrastructure for ergonomically representing PBT generators and
proving them correct.

If you want to make sure that a generator is correct, or if you plan to automate the production of
generators (e.g., via classical program synthesis or LLM automation), this library provides a
foundation.

Generator writers should look at the `Gen` module to see the operations available in generators. For
proving generators correct, look at `LawfulGen` and the examples in `BasaltExamples/`.

## Main Definitions

- `SPMF` — A type of sub-probability mass functions.
- `RandomChoice` — A type class capturing random choices.
- `Gen` — A type class capturing all of the operations necessary for PBT generators.
- `LawfulGen` - A type class capturing what it means for a `Gen` to be correct.
-/
