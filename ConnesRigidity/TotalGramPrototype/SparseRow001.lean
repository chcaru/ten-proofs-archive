


import ConnesRigidity.TotalGramPrototype.Row001Data

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem sparseRow001_check :
    (sparseSummary
        (termRow productRow001 totalRow001),
      absoluteTotal
        (termRow productRow001 totalRow001)) =
      (sparseRow001Expected, 567064858053168) := by
  unfold sparseSummary termRow absoluteTotal
    rangeSortTerms totalRow001 sparseRow001Expected
    productRow001
  decide +kernel

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity
