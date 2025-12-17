import Iris.BI.Classes
import Iris.BI.DerivedLaws
import Iris.BI.Extensions
import Iris.BI.Instances
import Iris.BI.BI
import Iris.BI.Notation
import Iris.BI.Updates

namespace Iris.BI
/-- Bidirectional entailment on separation logic propositions. -/
macro:25 P:term:29 " ⊣⊢ " Q:term:29 : term => ``(BiEntails iprop($P) iprop($Q))
