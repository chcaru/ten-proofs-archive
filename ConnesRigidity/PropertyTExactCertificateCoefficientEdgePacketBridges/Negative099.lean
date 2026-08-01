


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative099
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_099 :
    coefficientNegativePacketTerms099 =
      (negativeEdgeTerms.drop 50688).take 512 := by
  unfold coefficientNegativePacketTerms099 coefficientNegativePacketRows099
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
