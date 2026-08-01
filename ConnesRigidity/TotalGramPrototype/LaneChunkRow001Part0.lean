


import ConnesRigidity.TotalGramPrototype.ChunkRow001Part0Data

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem lane16Row001Part0_check :
    (laneSummary 16
        (termRow productRow001Part0 totalRow001Part0),
      absoluteTotal
        (termRow productRow001Part0 totalRow001Part0)) =
      (lane16Row001Part0Expected, 375840241443200) := by
  unfold laneSummary termRow absoluteTotal toLane
    rangeSortLanes collapseLanes
    totalRow001Part0 productRow001Part0 lane16Row001Part0Expected
  decide +kernel

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity
