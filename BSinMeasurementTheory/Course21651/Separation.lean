import Mathlib
import BSinMeasurementTheory.Course21651.BooleanHom

set_option linter.unusedSectionVars false

open Topology Set

namespace Course21651

namespace StoneRepresentation

variable (B : Type*) [BooleanAlgebra B]

instance : T2Space (StoneSpace B) := inferInstance

instance : TotallyDisconnectedSpace (StoneSpace B) := inferInstance

instance [Finite B] : CompactSpace (StoneSpace B) := inferInstance

end StoneRepresentation

end Course21651
