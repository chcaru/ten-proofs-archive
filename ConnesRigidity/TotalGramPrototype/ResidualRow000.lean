
import ConnesRigidity.TotalGramPrototype.Row001Data

namespace ConnesRigidity

namespace AffineSymplecticCertificate

namespace TotalGramPrototype

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

theorem residualRow000_check :
    residualCheckData 0 fullRow001 totalRow001 =
      (residualRow000Expected, 38203389288) := by
  unfold residualCheckData residualRow residualSlack
    offDiagonalAbsoluteTotal
    fullRow001 totalRow001 residualRow000Expected
  decide +kernel

end TotalGramPrototype

end AffineSymplecticCertificate

end ConnesRigidity
