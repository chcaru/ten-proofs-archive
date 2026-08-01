


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative046
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_046 :
    coefficientNegativePacketTerms046 =
      (negativeEdgeTerms.drop 23552).take 512 := by
  unfold coefficientNegativePacketTerms046 coefficientNegativePacketRows046
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
