


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive082
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_082 :
    coefficientPositivePacketTerms082 =
      (positiveEdgeTerms.drop 47232).take 576 := by
  unfold coefficientPositivePacketTerms082 coefficientPositivePacketRows082
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
