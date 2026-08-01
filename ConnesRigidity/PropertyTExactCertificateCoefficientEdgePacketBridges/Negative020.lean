


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative020
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_020 :
    coefficientNegativePacketTerms020 =
      (negativeEdgeTerms.drop 10240).take 512 := by
  unfold coefficientNegativePacketTerms020 coefficientNegativePacketRows020
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
