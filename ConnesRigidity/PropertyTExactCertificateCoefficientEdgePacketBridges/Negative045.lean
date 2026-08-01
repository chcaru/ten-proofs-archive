


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative045
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_045 :
    coefficientNegativePacketTerms045 =
      (negativeEdgeTerms.drop 23040).take 512 := by
  unfold coefficientNegativePacketTerms045 coefficientNegativePacketRows045
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
