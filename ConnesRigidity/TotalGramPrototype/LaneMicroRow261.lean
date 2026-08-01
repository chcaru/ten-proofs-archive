
import ConnesRigidity.TotalGramPrototype.MicroRow261Data

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem lane16Row261Micro16_check :
    (laneSummary 16
        (termRow productRow261Micro16 totalRow261Micro16),
      absoluteTotal
        (termRow productRow261Micro16 totalRow261Micro16)) =
      (lane16Row261Micro16Expected, 7813454373064) := by
  unfold laneSummary termRow absoluteTotal toLane
    rangeSortLanes collapseLanes
    totalRow261Micro16 productRow261Micro16 lane16Row261Micro16Expected
  decide +kernel

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity
