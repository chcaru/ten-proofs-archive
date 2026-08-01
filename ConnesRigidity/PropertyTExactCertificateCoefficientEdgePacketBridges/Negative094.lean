


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative094
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_094 :
    coefficientNegativePacketTerms094 =
      (negativeEdgeTerms.drop 48128).take 512 := by
  unfold coefficientNegativePacketTerms094 coefficientNegativePacketRows094
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
