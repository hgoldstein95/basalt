import Basalt.RandomChoice
import Basalt.Gen
import Basalt.IO
import Basalt.SPMF

/-!
# A Coinductive Model for Generators

This file presents a formal definiton of PBT generators that allows for first-class coinductive
fixed points.

## Background

We first provide some background on generator representations.

### QuickCheck
PBT generators have been defined in many ways over the years. The QuickCheck paper (Claessen and
Hughes, 2000) defines generators as:
```
def Gen α := Seed → α
```
This was the original "monadic" generator formulation (it uses a splittable RNG to define the monad
operations), and it works quite well operationally. However, this reprentation is a nightmare to
work with formally: any proofs about generators needs to reason explicitly about the mapping from
seeds to values. This representation also has the downside that important equivalences (e.g., the
monad laws) don't hold definitionally; they require a different definition of "distributional
equivalence."

### QuickChick
The first formalized representation of generaotrs comes from QuickChick (Paraskevopoulou et al.,
2015). In QuickChick, generators are still defined as above, but now the randomness is idealized and
axiomatized. The actual type that the authors use in most of their proofs is:
```
def Gen α := α → Prop -- (or Set α)
```
In other words, Paraskevopoulou et al. work with generators in terms of their _support_, or the set
of values that can be produced by the generator. Representing generators based on their support has
significant advantages for proofs, including the fact that the monad laws are true definitionally.

One downside of QuickChick's representation is that generators are required to terminate on all
paths, since generators are expressed as Rocq functions and Rocq that all functions terminate. The
authors get around this by adding a fuel parameter, allowing generators to fail if they run out of
fuel, but this is messy and makes it difficult to talk about termination as a first-class concept.

### Free Generators
As mentioned above, QuickChick's formalism relates the executable representation (`Seed → α`) with
the proof representation (`Set α`) via axioms about the underlying RNG. _Free generators_ (Goldstein
and Pierce, 2022) generalize over both of these representations and talk about generators as more
abstract objects. Free generators are defined as having three operations, `Return`, `Bind`, and
`Pick` (which represents a weighted random choice). These operations are opaque, and can be mapped
to concrete operations as needed. This means that a free generator can be interpreted as either a
QuickCheck style operational generator or as a QuickChick style support set.

## Our Representation

Our representation borrows ideas from all of the above representations.
- Our core definition of generators allows for multiple interpretations, much like free generators.
- We provide an executable interpretation (like QuickChick's) in terms Lean's standard RNG.
- We provide a proof-optimized interpretation (like QuickChick's) in terms of sub-probability mass
  functions.

The key differences are as follows:
1. Our proof interpretation directly captures generator distributions, meaning that proofs can talk
   about _how often_ a generator produces particular values.
2. Our representation can express potentially non-terminating generators and provides first-class
   support for proving termination, including almost-sure termination.
-/
