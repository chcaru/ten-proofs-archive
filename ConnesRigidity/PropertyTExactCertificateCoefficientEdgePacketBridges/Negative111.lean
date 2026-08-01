


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative111
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_111 :
    coefficientNegativePacketTerms111 =
      (negativeEdgeTerms.drop 56832).take 512 := by
  unfold coefficientNegativePacketTerms111 coefficientNegativePacketRows111
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
