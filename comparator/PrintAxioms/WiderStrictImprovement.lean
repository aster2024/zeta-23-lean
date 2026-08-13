/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Width-six four-point strict-improvement axiom audit:

  lake env lean comparator/PrintAxioms/WiderStrictImprovement.lean

This file audits both the wider endpoint theorem and the exact fixed-interface
ceiling.  Both modules are imported by the library root; the pinned build and
this audit are still required before either source candidate is called
formally certified.
-/
import Zeta23.StrictImprovement.ZetaWiderEndpointPassage
import Zeta23.StrictImprovement.WiderFixedInterfaceCeiling
import Zeta23.StrictImprovement.DirectFourPointInterface

#print axioms Zeta23.StrictImprovement.zeta_wider_strict_simple_endpoint_rational
#print axioms Zeta23.StrictImprovement.common_budget_iff_le_widerFixedDeltaCeiling
#print axioms Zeta23.StrictImprovement.direct_six_edge_energy_stable
#print axioms Zeta23.StrictImprovement.directFourEtaLower_le_endpoint_gain
