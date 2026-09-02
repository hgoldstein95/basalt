/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Michael Hicks
-/
import Basalt.PBT.Property
import Basalt.PBT.Campaign
import Basalt.PBT.Driver

/-!
# Property-Based Testing

Basalt's generators are the inputs of property-based tests; this is the other half — stating a
property and running it. A property is a generator of `TestOutcome` and so is polymorphic in its
monad, which means one property term is testable at every interpretation of `Gen`, and a campaign is
just that term run at a chosen one.

## Main Definitions

- `TestOutcome`, `check` / `checkWith` / `assume` / `forAll` — stating a property.
- `Property` — a property before an interpretation is chosen.
- `CampaignReport`, `campaign` — running one, and the failure contract every backend shares.
- `Backend`, `dispatch` — a command-line front end over named properties.
-/
