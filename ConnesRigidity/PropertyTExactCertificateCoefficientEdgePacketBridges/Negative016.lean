


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Negative016
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientNegativePacketTermsBridge_016 :
    coefficientNegativePacketTerms016 =
      (negativeEdgeTerms.drop 8192).take 512 := by
  unfold coefficientNegativePacketTerms016 coefficientNegativePacketRows016
  unfold coefficientNegativePacketsTerms
  unfold coefficientNegativePacketTerms
    decodeCoefficientNegativePacket
    coefficientNegativeDecodedPacketTerms coefficientEdgeTerm
  unfold negativeEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
