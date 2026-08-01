


import ConnesRigidity.TotalGramPrototype.Row261Data

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in


theorem residualRow260_check :
    residualCheckData 260 fullRow261 totalRow261 =
      (residualRow260Expected, 39628309984) := by
  unfold residualCheckData residualRow residualSlack
    offDiagonalAbsoluteTotal
    fullRow261 totalRow261 residualRow260Expected
  decide +kernel

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity
