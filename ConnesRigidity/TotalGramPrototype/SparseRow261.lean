


import ConnesRigidity.TotalGramPrototype.Row261Data

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem sparseRow261_check :
    (sparseSummary
        (termRow productRow261 totalRow261),
      absoluteTotal
        (termRow productRow261 totalRow261)) =
      (sparseRow261Expected, 46555298542464) := by
  unfold sparseSummary termRow absoluteTotal
    rangeSortTerms totalRow261 sparseRow261Expected
    productRow261
  decide +kernel

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity
