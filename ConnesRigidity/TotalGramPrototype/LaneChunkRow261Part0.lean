


import ConnesRigidity.TotalGramPrototype.ChunkRow261Part0Data

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem lane16Row261Part0_check :
    (laneSummary 16
        (termRow productRow261Part0 totalRow261Part0),
      absoluteTotal
        (termRow productRow261Part0 totalRow261Part0)) =
      (lane16Row261Part0Expected, 14382956960176) := by
  unfold laneSummary termRow absoluteTotal toLane
    rangeSortLanes collapseLanes
    totalRow261Part0 productRow261Part0 lane16Row261Part0Expected
  decide +kernel

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity
