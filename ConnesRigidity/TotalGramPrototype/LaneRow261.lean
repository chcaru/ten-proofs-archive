


import ConnesRigidity.TotalGramPrototype.Row261Data

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in


theorem lane16Row261_check :
    (laneSummary 16
        (termRow productRow261 totalRow261),
      absoluteTotal
        (termRow productRow261 totalRow261)) =
      (lane16Row261Expected, 46555298542464) := by
  unfold laneSummary termRow absoluteTotal toLane
    rangeSortLanes collapseLanes
    totalRow261 lane16Row261Expected productRow261
  decide +kernel

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity
