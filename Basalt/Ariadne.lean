import Basalt.Gen
import Basalt.Combinators
import Basalt.Tuning.Basic
import Basalt.Tuning.Attr
import Basalt.IO

@[tunable]
def genBool [Gen G] : G Bool :=
  frequency! [
    (1, fun () => return True),
    (1, fun () => return False)
  ]

def tune (steps : ℕ) (loss : List α → Float) (g : Tuning → IO α) :
    Tuning → IO α := sorry

#check genBool.defaults

#check tune
  (steps := 100)
  (loss := fun samples => (samples.filter id).length.toFloat)
  (g := genBool.tuned)
  genBool.defaults
