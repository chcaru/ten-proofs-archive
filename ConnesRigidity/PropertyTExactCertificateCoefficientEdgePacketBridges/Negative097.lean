


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative097
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_097 :
    coefficientNegativePacketTerms097 =
      (negativeEdgeTerms.drop 49664).take 512 := by
  unfold coefficientNegativePacketTerms097 coefficientNegativePacketRows097
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
