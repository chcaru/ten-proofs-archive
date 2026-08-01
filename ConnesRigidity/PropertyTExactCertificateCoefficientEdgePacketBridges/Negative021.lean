


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative021
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_021 :
    coefficientNegativePacketTerms021 =
      (negativeEdgeTerms.drop 10752).take 512 := by
  unfold coefficientNegativePacketTerms021 coefficientNegativePacketRows021
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
