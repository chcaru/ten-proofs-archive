
import ConnesRigidity.TotalGramPrototype.Row001Data

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem lane16Row001_check :
    (laneSummary 16
        (termRow productRow001 totalRow001),
      absoluteTotal
        (termRow productRow001 totalRow001)) =
      (lane16Row001Expected, 567064858053168) := by
  unfold laneSummary termRow absoluteTotal toLane
    rangeSortLanes collapseLanes
    totalRow001 lane16Row001Expected productRow001
  decide +kernel

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity
