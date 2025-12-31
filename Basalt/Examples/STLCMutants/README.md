## STLC Mutants

(Taken from the Etna artifact)

Base file: 
- `STLC.lean`: Contains type definitions (`Typ, Expr, Ctx`) and shared functions (`isNF, getTyp, typeCheck`)

Mutants
- `STLC0.lean`: Correct implementation
- `STLC1.lean`: Bug `shift_var_none` (doesn't shift any variables)
- `STLC2.lean`: Bug `shift_var_all` (shifts all variables without checking cutoff)
- `STLC3.lean`: Bug `shift_var_leq` (uses <= instead of < for cutoff)
- `STLC4.lean`: Bug `shift_abs_no_incr` (doesn't increment cutoff in Abs case)
- `STLC5.lean`: Bug `subst_var_all` (substitutes all variables)
- `STLC6.lean`: Bug `subst_var_none` (doesn't substitute any variables)
- `STLC7.lean`: Bug `subst_abs_no_shift` (doesn't shift s in Abs case)
- `STLC8.lean`: Bug `subst_abs_no_incr` (doesn't increment n in Abs case)
- `STLC9.lean`: Bug `substTop_no_shift` (doesn't shift at all)
- S`TLC10.lean`: Bug `substTop_no_shift_back` (doesn't shift back after substitution)