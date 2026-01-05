/-- Boolean implication: `A ==> B` is equivalent to `¬A ∨ B` -/
def boolImplies (a b : Bool) : Bool := !a || b
